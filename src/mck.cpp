#include <cxxabi.h>
#include <dlfcn.h>
#include <errno.h>
#include <execinfo.h>
#include <pthread.h>
#include <semaphore.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

#define MAX_PATH 4096

#define STACK_MAX_DEPTH 32          // 最大记录调用栈深度
#define STACK_MAX_SAVE (100 * 1024) // 最大记录调用栈数量
#define STACK_HASH_SIZE 1231313     // STACK hash节点数量

#define SUMMARY_STACK_COUNT 1024    // 输出调用栈数量
#define SUMMARY_TRIGGER_TIMER 300   // 定时输出间隔
#define SUMMARY_TRIGGER_SIG SIGUSR2 // 信号触发输出

#define OPERATION_SAVE_COUNT (1024 * 8) //记录最近的内存操作数量

#define VERSION "0.1"

#define MY_HEAP_SIZE (2 * 1024 * 1024)
#define ALIGN(x) ((x + (sizeof(size_t) - 1)) & ~(sizeof(size_t) - 1))

// 调用栈信息
typedef struct stack {
  struct stack* next;          // 单链表
  void* addr[STACK_MAX_DEPTH]; // 调用栈
  int32_t depth;               // 调用栈深度
  uint32_t allocs;             // 分配次数
  uint32_t frees;              // 释放次数
  uint64_t size;               // 剩余内存总数
} STACK;

// hash表头结点
typedef struct {
  STACK* head;
} BUCKET;

// mmap 地址记录
typedef struct map_area {
  struct map_area* ma_next;
  unsigned long start;
  unsigned long end;
  STACK* stack;
} MAP_AREA;

#define MY_MAGIC_ALLOC 0x55aa66bb77cc88dd // 已分配内存魔术字
#define MY_MAGIC_FREE 0xdd88cc77bb66aa55  // 已释放内存魔数字

typedef struct {
  size_t magic;
  void* realptr;
  STACK* stack;
  size_t size;
} MY_HEAD;

typedef enum {
  MF_MALLOC,
  MF_FREE,
  MF_CALLOC,
  MF_REALLOC,
  MF_REALLOC_FREE_OLD,
  MF_REALLOC_FREE_ZERO,
  MF_MEMALIGN,
  MF_VALLOC,
  MF_MMAP,
  MF_MUNMAP
} MC_FUNC;

typedef struct {
  void* ptr;
  size_t size;
  STACK* stack;
  MC_FUNC call;
} POINTER;

/*----------------------------------------------------------------------------------*/

namespace memchecker {

//线程变量，用于避免内部函数调用malloc时引起递归
__thread int inner_call;
int initted;
int enable_log;

#define mc_log(fmt, args...)                     \
  do {                                           \
    if (enable_log) {                            \
      printf("[mem_checker] " fmt "\n", ##args); \
    }                                            \
  } while (0)

//被hook的函数指针
void* (*malloc_func)(size_t size);
void (*free_func)(void* ptr);
void* (*calloc_func)(size_t nmemb, size_t size);
void* (*realloc_func)(void* ptr, size_t size);
void* (*memalign_func)(size_t boundary, size_t size);
void* (*mmap_func)(void* addr, size_t len, int prot, int flags, int fildes, off_t off);
int (*munmap_func)(void* addr, size_t len);

int (*libunw_backtrace)(void** buffer, int size);
void* libunwind_handle;

BUCKET* stack_hash;
uint32_t stack_hash_size = STACK_HASH_SIZE;
uint32_t max_stack_saved = STACK_MAX_SAVE;
uint32_t stack_depth     = STACK_MAX_DEPTH;
uint32_t stack_saved;
uint32_t stack_losted; // 未记录的调用栈数

MAP_AREA* mmap_list; // mmap分配内存链表
volatile int mmap_lock = 0;

POINTER* pointer_ring;
volatile int pointer_ring_lock = 0;
uint32_t pointer_ring_size     = OPERATION_SAVE_COUNT;
uint32_t pointer_ring_index;

char output_directory[MAX_PATH] = "./";
uint32_t summary_file_id;
uint32_t max_stack_report = SUMMARY_STACK_COUNT;

int report_trigger_sig = SUMMARY_TRIGGER_SIG;
pthread_t report_thread;
sem_t report_sem;
int report_run_flag;
int report_trigger_timer = SUMMARY_TRIGGER_TIMER;
int report_stack_all     = 0;

sighandler_t old_handler;

char my_heap[MY_HEAP_SIZE];
size_t my_heap_pos;

/*-------------------------------------------------------------------------------------------*/

void mem_checker_init();
int stack_hash_init();
void stack_hash_clean();
int stack_report_init();
void stack_report_clean();
void* report_proc(void* arg);
void build_report();
void my_sighandler(int);
void get_environment();
void write_summary(STACK* stacks[], uint32_t count);
int pointer_ring_init();
void pointer_ring_clean();

struct MIN_HEAP;
MIN_HEAP* min_heap_create(uint32_t capacity);
void min_heap_destroy(MIN_HEAP* q);
int min_heap_pop(MIN_HEAP* q, void** data);
void min_heap_push(MIN_HEAP* q, long key, void* data);
void symbol_format(char* buf, size_t size, char* symbol, int index, void* addr);

int storage_init() {
  if (stack_hash_init() ||
      pointer_ring_init()) {
    return -1;
  }
  return 0;
}

void storage_clean() {
  pointer_ring_clean();
  stack_hash_clean();
}

int pointer_ring_init() {
  if (!pointer_ring_size) {
    return 0;
  }

  pointer_ring = (POINTER*)calloc_func(1,
      sizeof(POINTER) * pointer_ring_size);
  return pointer_ring ? 0 : -1;
}

void pointer_ring_clean() {
  // todo clean
}

inline __attribute__((always_inline)) void save_ptr(void* ptr_, size_t size_, STACK* stack_, MC_FUNC call_) {
  if (pointer_ring) {
    while (__sync_lock_test_and_set(&pointer_ring_lock, 1))
      ;
    POINTER* p = pointer_ring + pointer_ring_index;
    p->stack   = stack_;
    p->size    = size_;
    p->ptr     = ptr_;
    p->call    = call_;
    if (++pointer_ring_index == pointer_ring_size) {
      pointer_ring_index = 0;
    }
    __sync_lock_release(&pointer_ring_lock);
  }
}

int stack_hash_init() {
  stack_hash = (BUCKET*)calloc_func(sizeof(BUCKET), stack_hash_size);
  if (!stack_hash) {
    mc_log("alloc stack hash fail");
    return -1;
  }
  return 0;
}

// 不释放统计资源, 避免存在其他destructor函数继续分配释放内存
void stack_hash_clean() {
  if (!stack_hash) {
    return;
  }

  for (unsigned i = 0; i < stack_hash_size; i++) {
    BUCKET* bucket = &stack_hash[i];
    STACK* stack   = bucket->head;
    bucket->head   = NULL;
    while (stack) {
      STACK* next = stack->next;
      if (stack->size) {
        printf("leak stack [%p]:\n", stack);
        char** symbols = backtrace_symbols(stack->addr, stack->depth);
        if (symbols) {
          for (int j = 0; j < stack->depth && symbols[j]; j++) {
            char buf[2048];
            buf[sizeof(buf) - 1] = 0;
            symbol_format(buf, sizeof(buf) - 1, symbols[j], j, stack->addr[j]);
            printf("%s\n", buf);
          }
          free(symbols);
        }
        printf("allocs(%u) frees(%u) hold(%lu)\n\n",
            stack->allocs, stack->frees, stack->size);
      }
      stack = next;
    }
  }
}

// TODO: hash算法简化
inline uint32_t hash(void* addr[], int depth) {
  uint32_t val = 0;
  for (int i = 0; i < depth; i++) {
    unsigned long tmp = (unsigned long)addr[i];
    val ^= tmp;
  }
  return val % stack_hash_size;
}

inline int stack_equal(void* addr1[], int depth1, void* addr2[], int depth2) {
  if (depth1 != depth2) {
    return 0;
  }

  for (int i = 0; i < depth1; i++) {
    if (addr1[i] != addr2[i]) {
      return 0;
    }
  }
  return 1;
}

inline STACK* callstack_update(void* addr[], int depth, size_t size) {
  uint32_t index = hash(addr, depth);
  BUCKET* bucket = &stack_hash[index];

  STACK* stack = bucket->head;
  while (stack) {
    if (stack_equal(stack->addr, stack->depth, addr, depth)) {
      break;
    }
    stack = stack->next;
  }

  if (stack) {
    __sync_add_and_fetch(&stack->allocs, 1);
    __sync_add_and_fetch(&stack->size, size);
    return stack;
  }

  if (max_stack_saved <= stack_saved) {
    __sync_add_and_fetch(&stack_losted, 1);
    mc_log("reach max stack count");
    return NULL;
  }

  stack = (STACK*)malloc_func(sizeof(STACK));
  if (!stack) {
    mc_log("alloc STACK fail");
    return NULL;
  }

  memcpy(stack->addr, addr, sizeof(void*) * depth);
  stack->depth  = depth;
  stack->allocs = 1;
  stack->frees  = 0;
  stack->size   = size;

  //!!多线程可能同时插入两个相同调用栈, 不影响统计
  do {
    stack->next = bucket->head;
  } while (!__sync_bool_compare_and_swap(&bucket->head, stack->next, stack));

  __sync_add_and_fetch(&stack_saved, 1);

  return stack;
}

int stack_report_init() {
  if (sem_init(&report_sem, 0, 0)) {
    mc_log("sem_init: %s", strerror(errno));
    return -1;
  }

  report_run_flag = 1;
  if (pthread_create(&report_thread, NULL, report_proc, NULL)) {
    mc_log("pthread_create: %s", strerror(errno));
    sem_destroy(&report_sem);
    return -1;
  }

  old_handler = signal(report_trigger_sig, my_sighandler);

  return 0;
}

void stack_report_clean() {
  if (report_thread) {
    signal(SUMMARY_TRIGGER_SIG, old_handler);
    report_run_flag = 0;
    sem_post(&report_sem);

    pthread_join(report_thread, NULL);

    report_thread = 0;
    sem_destroy(&report_sem);
  }
}

void my_sighandler(int) {
  sem_post(&report_sem);
}

#define WAIT_MS 1000ULL

void* report_proc(void* arg) {
  int wait_ms = 0;

  while (report_run_flag) {
    struct timespec ts;
    (void)clock_gettime(CLOCK_REALTIME, &ts);
    ts.tv_nsec = (ts.tv_nsec + WAIT_MS * 1000000) % 1000000000;
    ts.tv_sec += (ts.tv_nsec + WAIT_MS * 1000000) / 1000000000;

    int s;
    while ((s = sem_timedwait(&report_sem, &ts)) == -1 &&
           errno == EINTR) {
      continue;
    }

    if (!report_run_flag) {
      break;
    }

    // 信号量触发
    if (s == 0) {
      build_report();
      continue;
    }

    // 定时触发
    if (errno == ETIMEDOUT &&
        report_trigger_timer > 0) {
      wait_ms += WAIT_MS;
      if (wait_ms / 1000 >= report_trigger_timer) {
        build_report();
        wait_ms = 0;
      }
    }
  }

  return NULL;
}

void build_report() {
  mc_log("build report:");

  uint32_t to_report = report_stack_all ? stack_saved : max_stack_report;

  MIN_HEAP* queue = min_heap_create(to_report);
  if (!queue) {
    mc_log("create min heap fail %u", to_report);
    return;
  }

  STACK** stacks = (STACK**)malloc(sizeof(STACK*) * to_report);
  if (!stacks) {
    mc_log("alloc stack* buffer fail");
    min_heap_destroy(queue);
    return;
  }

  for (unsigned i = 0; i < stack_hash_size; i++) {
    STACK* stack = stack_hash[i].head;
    while (stack) {
      if (stack->size || report_stack_all) {
        min_heap_push(queue, stack->size, stack);
      }
      stack = stack->next;
    }
  }

  uint32_t count = 0;
  while (!min_heap_pop(queue, (void**)&stacks[count])) {
    count++;
  }

  write_summary(stacks, count);

  min_heap_destroy(queue);
  free(stacks);
}

int get_exe(char* buffer, size_t size) {
  char proc_path[256] = {0};
  snprintf(proc_path, sizeof(proc_path) - 1, "/proc/%d/exe", getpid());

  char exe_path[MAX_PATH] = {0};
  if (0 > readlink(proc_path, exe_path, sizeof(exe_path) - 1)) {
    return -1;
  }

  const char* pos = strrchr(exe_path, '/');
  if (!pos) {
    return -1;
  }

  strncpy(buffer, pos + 1, size);
  return 0;
}

void write_summary(STACK* stacks[], uint32_t count) {
  char exe[256] = {0};
  get_exe(exe, sizeof(exe) - 1);

  char fname[MAX_PATH] = {0};
  snprintf(fname, MAX_PATH - 1, "%s/%s-%d-%u.dat", output_directory, exe, getpid(), summary_file_id++);

  FILE* fp = fopen(fname, "w");
  if (!fp) {
    mc_log("open file %s fail\n", fname);
    return;
  }

  fprintf(fp, "*************************************************\n"
              "memory checker ver:%s build:%s %s\n"
              "*************************************************\n"
              "process:(%d)\n"
              "saved stacks:(%u)\n"
              "lost  stacks:(%u)\n"
              "log enable:(%s)\n"
              "max stack saved:(%u)\n"
              "max stack report:(%u)\n"
              "stack hashsize:(%u)\n"
              "report trigger sig:(%d)\n"
              "report trigger timer:(%d)\n"
              "output directory:(%s)\n"
              "*************************************************\n",
      VERSION, __TIME__, __DATE__,
      getpid(),
      stack_saved,
      stack_losted,
      enable_log ? "true" : "false",
      max_stack_saved,
      report_stack_all ? max_stack_saved : max_stack_report,
      stack_hash_size,
      report_trigger_sig,
      report_trigger_timer,
      output_directory);

  for (uint32_t i = 1; i <= count; i++) {
    STACK* stack = stacks[count - i];

    fprintf(fp, "callstack[%u] [%p]:\n", i, stack);
    char** symbols = backtrace_symbols(stack->addr, stack->depth);
    if (symbols) {
      for (int j = 0; j < stack->depth && symbols[j]; j++) {
        char buf[2048];
        buf[sizeof(buf) - 1] = 0;
        symbol_format(buf, sizeof(buf) - 1, symbols[j], j, stack->addr[j]);
        fprintf(fp, "%s\n", buf);
      }
      free(symbols);
    }
    fprintf(fp, "allocs(%u) frees(%u) hold(%lu)\n\n",
        stack->allocs, stack->frees, stack->size);
  }

  fclose(fp);
}

/*
 * backtrace_symbols 输出格式
   backtrace() returned 8 addresses
    ./myso.so(+0x87cba)  [0x80587f0]
    ./prog(myfunc3+0x5c) [0x80487f0]
    ./prog [0x8048871]
    ./prog(myfunc+0x21) [0x8048894]
    ./prog(myfunc+0x1a) [0x804888d]
    ./prog(myfunc+0x1a) [0x804888d]
    ./prog(main+0x65) [0x80488fb]
    /lib/libc.so.6(__libc_start_main+0xdc) [0xb7e38f9c]
    ./prog [0x8048711]


  1、修正C++名字改编
  2、调整输出顺序：         #序号 返回地址 函数名          模块名(TODO: 整改为 源码 + 行号)
 */
void symbol_format(char* buf, size_t buf_size, char* symbol, int index, void* addr) {
  char* paren_l = NULL;
  char* paren_r = NULL;
  char* plus    = NULL;

  for (char* p = symbol; *p; ++p) {
    if (*p == '(') {
      paren_l = p;
    } else if (*p == '+') {
      plus = p;
    } else if (*p == ')') {
      paren_r = p;
      if (paren_l) {
        break;
      }
    }
  }

  const char* module   = symbol;
  const char* function = "";
  const char* offset   = NULL;

  if (paren_l && paren_r && paren_r > paren_l) {
    *paren_l = 0;
    *paren_r = 0;
    function = paren_l + 1;

    if (plus) {
      *plus  = 0;
      offset = plus + 1;
    }

    if (!function[0] && offset) {
      // 无函数名, 只有模块偏移
      // TODO: 根据offset 和 module 计算函数
    }
  }

  int status      = 0;
  char* real_name = abi::__cxa_demangle(function, 0, 0, &status);

  if (offset) {
    snprintf(buf, buf_size, "#%-2d 0x%016lx (%s+%s) %s",
        index,
        (unsigned long)addr,
        real_name ? real_name : function,
        offset,
        module);
  } else {
    snprintf(buf, buf_size, "#%-2d 0x%016lx (%s) %s",
        index,
        (unsigned long)addr,
        real_name ? real_name : function,
        module);
  }

  if (real_name) {
    free(real_name);
  }
}

void get_environment() {
  char* env = getenv("MC_DEBUG");
  if (env && !strcasecmp(env, "on")) {
    enable_log = 1;
    mc_log("mem checker set log 'ON'");
  }

  if ((env = getenv("MC_STACK_SAVE"))) {
    max_stack_saved = (uint32_t)strtol(env, NULL, 10);
    mc_log("max_stack_saved=%u", max_stack_saved);
  }

  if ((env = getenv("MC_STACK_HASH"))) {
    uint32_t val = (uint32_t)strtol(env, NULL, 10);
    if (val) {
      stack_hash_size = val;
      mc_log("stack_hash_size=%u", stack_hash_size);
    }
  }

  if ((env = getenv("MC_STACK_DEPTH"))) {
    uint32_t val = (uint32_t)strtol(env, NULL, 10);
    if (val && val < STACK_MAX_DEPTH) {
      stack_depth = val;
      mc_log("stack_depth=%u", stack_depth);
    }
  }

  if ((env = getenv("MC_STACK_REPORT"))) {
    uint32_t val = (uint32_t)strtol(env, NULL, 10);
    if (val) {
      max_stack_report = val;
      mc_log("max_stack_report=%u", max_stack_report);
    }
  }

  if ((env = getenv("MC_REPORT_TRIGGER"))) {
    int val = (int)strtol(env, NULL, 10);
    if (val) {
      report_trigger_sig = val;
      mc_log("report_trigger_sig=%d", report_trigger_sig);
    }
  }

  if ((env = getenv("MC_REPORT_TIMER"))) {
    int val              = (int)strtol(env, NULL, 10);
    report_trigger_timer = val;
    mc_log("report_trigger_timer=%d", report_trigger_timer);
  }

  if ((env = getenv("MC_REPORT_ALL"))) {
    int val          = (int)strtol(env, NULL, 10);
    report_stack_all = val;
    mc_log("report_stack_all=%d", report_stack_all);
  }

  if ((env = getenv("MC_POINTER_SAVE"))) {
    uint32_t val      = (uint32_t)strtol(env, NULL, 10);
    pointer_ring_size = val;
    mc_log("pointer_ring_size=%u", pointer_ring_size);
  }

  if ((env = getenv("MC_OUTPUT_DIR"))) {
    strncpy(output_directory, env, sizeof(output_directory) - 1);
    mc_log("output_directory=%s", output_directory);
  }
}

/*-----------------------------------------------------------------------------*/

void* my_malloc(size_t size) {
  size_t alloc_size = ALIGN(size) + sizeof(size_t);
  if (MY_HEAP_SIZE - my_heap_pos >= alloc_size) {
    char* p     = my_heap + my_heap_pos;
    *(size_t*)p = size;
    p += sizeof(size_t);
    my_heap_pos += alloc_size;

    return p;
  }
  return NULL;
}

void my_free(void* ptr) {
  // do nothing
}

void* my_calloc(size_t nmemb, size_t size) {
  size_t alloc_size = ALIGN(nmemb * size) + sizeof(size_t);

  if (MY_HEAP_SIZE - my_heap_pos >= alloc_size) {
    char* p     = my_heap + my_heap_pos;
    *(size_t*)p = (nmemb * size);
    p += sizeof(size_t);
    my_heap_pos += alloc_size;

    memset(p, 0, nmemb * size);
    return p;
  }

  return NULL;
}

void* my_realloc(void* ptr, size_t size) {
  size_t alloc_size = ALIGN(size) + sizeof(size_t);

  if (MY_HEAP_SIZE - my_heap_pos >= alloc_size) {
    char* p     = my_heap + my_heap_pos;
    *(size_t*)p = size;
    p += sizeof(size_t);
    my_heap_pos += alloc_size;

    if (ptr) {
      size_t old_size = *(size_t*)(((char*)ptr) - sizeof(size_t));
      memcpy(p, ptr, old_size);
    }
    return p;
  }
  return NULL;
}

inline __attribute__((always_inline)) int back_trace(void** buffer, int size) {
  if (libunw_backtrace) {
    return libunw_backtrace(buffer, size);
  }
  return backtrace(buffer, size);
}

/*--------------------------------------------------------------------------------*/

inline void mmap_list_lock() {
  while (__sync_lock_test_and_set(&mmap_lock, 1)) {
  }
}

inline void mmap_list_unlock() {
  __sync_lock_release(&mmap_lock);
}

/*
 * 按照地址区间从低到高插入链表
 */
inline void __reg_mm_area(MAP_AREA* mma) {
  MAP_AREA** pprev = &mmap_list;
  MAP_AREA* next   = mmap_list;

  while (next) {
    if (mma->start < next->start) {
      break;
    }

    pprev = &next->ma_next;
    next  = next->ma_next;
  }

  *pprev       = mma;
  mma->ma_next = next;
}

inline void reg_mm_area(MAP_AREA* mma) {
  mmap_list_lock();
  __reg_mm_area(mma);
  mmap_list_unlock();
}

/*
 * 查找地址 addr 所属的 MAP_AREA
 */
inline MAP_AREA* __find_mm_area(unsigned long addr, MAP_AREA** pprev) {
  MAP_AREA* mma  = mmap_list;
  MAP_AREA* prev = NULL;

  while (mma) {
    if (addr >= mma->start && addr < mma->end) {
      break;
    }

    prev = mma;
    mma  = mma->ma_next;
  }

  if (pprev) {
    *pprev = prev;
  }

  return mma;
}

inline void __split_mm_area(MAP_AREA* mma, unsigned long addr) {
  MAP_AREA* new_area = (MAP_AREA*)malloc_func(sizeof(MAP_AREA));

  if (mma->stack) {
    __sync_add_and_fetch(&mma->stack->allocs, 1);
  }

  *new_area       = *mma;
  new_area->start = addr;

  mma->end     = addr;
  mma->ma_next = new_area;
}

/*  [ first,  last ]  */
inline void __update_mmap_stacks(MAP_AREA* first, MAP_AREA* last) {
  MAP_AREA* mma = first;
  while (mma) {
    if (mma->stack) {
      __sync_add_and_fetch(&mma->stack->frees, 1);
      __sync_sub_and_fetch(&mma->stack->size, (mma->end - mma->start));
    }

    if (mma == last) {
      break;
    }

    mma = mma->ma_next;
  }
}

/* 释放 (prev, last] */
inline void __free_mmap_areas(MAP_AREA* prev, MAP_AREA* last) {
  MAP_AREA** pprev = prev ? &prev->ma_next : &mmap_list;

  MAP_AREA* mma = *pprev;
  *pprev        = last ? last->ma_next : NULL;

  while (mma) {
    MAP_AREA* next = mma->ma_next;
    free_func(mma);

    if (mma == last) {
      break;
    }
    mma = next;
  }
}

inline void __unreg_mm_area(unsigned long start, size_t len) {
  MAP_AREA* prev = NULL;
  MAP_AREA* mma  = __find_mm_area(start, &prev);

  if (!mma) {
    return;
  }

  unsigned long end = start + len;
  if (end <= mma->start) {
    return;
  }

  if (start > mma->start) {
    __split_mm_area(mma, start);
    prev = mma;
  }

  MAP_AREA* last = __find_mm_area(end - 1, NULL);
  if (last && last->end > end) {
    __split_mm_area(last, end);
  }

  mma = prev ? prev->ma_next : mmap_list;

  __update_mmap_stacks(mma, last);
  __free_mmap_areas(prev, last);
}

inline void unreg_mm_area(unsigned long start, size_t len) {
  mmap_list_lock();
  __unreg_mm_area(start, len);
  mmap_list_unlock();
}

/*-------------------------------------------------------------------------------------*/

void __attribute__((constructor)) mem_checker_init() {
  if (initted) {
    return;
  }
  initted = 1;

  // printf/dlsym ...函数中可能调用到malloc free，先用自己的简单实现代替
  malloc_func  = my_malloc;
  free_func    = my_free;
  calloc_func  = my_calloc;
  realloc_func = my_realloc;

  inner_call = 1;

  printf("mem checker init....\n");

  void* (*tmp_malloc)(size_t size);
  void (*tmp_free)(void* ptr);
  void* (*tmp_calloc)(size_t nmemb, size_t size);
  void* (*tmp_realloc)(void* ptr, size_t size);
  void* (*tmp_memalign)(size_t align, size_t size);
  void* (*tmp_mmap)(void* addr, size_t len, int prot, int flags,
      int fildes, off_t off);
  int (*tmp_munmap)(void* addr, size_t len);

  *(void**)(&tmp_malloc)   = dlsym(RTLD_NEXT, "malloc");
  *(void**)(&tmp_free)     = dlsym(RTLD_NEXT, "free");
  *(void**)(&tmp_calloc)   = dlsym(RTLD_NEXT, "calloc");
  *(void**)(&tmp_realloc)  = dlsym(RTLD_NEXT, "realloc");
  *(void**)(&tmp_memalign) = dlsym(RTLD_NEXT, "memalign");
  *(void**)(&tmp_mmap)     = dlsym(RTLD_NEXT, "mmap");
  *(void**)(&tmp_munmap)   = dlsym(RTLD_NEXT, "munmap");

  if (!tmp_malloc || !tmp_free || !tmp_calloc ||
      !tmp_realloc || !tmp_memalign || !tmp_mmap || !tmp_munmap) {
    printf("load function fail %s\n", dlerror());
    exit(-1);
  }

  malloc_func   = tmp_malloc;
  free_func     = tmp_free;
  calloc_func   = tmp_calloc;
  realloc_func  = tmp_realloc;
  memalign_func = tmp_memalign;
  mmap_func     = tmp_mmap;
  munmap_func   = tmp_munmap;

  get_environment();

  if (storage_init()) {
    exit(-1);
  }

  inner_call = 0;

  // 加载libunwind 库
  libunwind_handle = dlopen("libunwind.so", RTLD_NOW);
  if (libunwind_handle) {
    *(void**)(&libunw_backtrace) = dlsym(libunwind_handle, "unw_backtrace");
    if (libunw_backtrace) {
      printf("use unw_backtrace in libunwind.so\n");
    }
  }

  if (stack_report_init()) {
    exit(-1);
  }

  mc_log("mem checker init success");
}

void __attribute__((destructor)) mem_checker_clean() {
  stack_report_clean();

  inner_call = 1;

  if (libunw_backtrace) {
    dlclose(libunwind_handle);
    libunwind_handle = NULL;
    libunw_backtrace = NULL;
  }

  storage_clean();
  inner_call = 0;
}

/*-----------------------------------------------------------------------------------*/

/* 使用最小堆构造队列 */

typedef struct {
  uint64_t key;
  void* data;
} ITEM;

typedef struct MIN_HEAP {
  uint32_t size;
  uint32_t capacity;
  ITEM items[0];
} MIN_HEAP;

inline void swap(ITEM* it1, ITEM* it2) {
  ITEM tmp = *it1;
  *it1     = *it2;
  *it2     = tmp;
}

MIN_HEAP* min_heap_create(uint32_t capacity) {
  size_t alloc_size = sizeof(MIN_HEAP) + sizeof(ITEM) * (capacity + 2);

  MIN_HEAP* q = (MIN_HEAP*)malloc(alloc_size);
  if (!q) {
    return NULL;
  }

  for (uint32_t i = 0; i < capacity + 2; i++) {
    q->items[i].key = (uint64_t)-1;
  }

  q->size     = 0;
  q->capacity = capacity;

  return q;
}

void min_heap_destroy(MIN_HEAP* q) {
  if (q) {
    free(q);
  }
}

int min_heap_pop(MIN_HEAP* q, void** data) {
  if (!q->size) {
    return -1;
  }

  if (data) {
    *data = q->items[1].data;
  }

  swap(&q->items[1], &q->items[q->size]);
  q->items[q->size].key = (uint64_t)(-1);
  q->size--;

  uint32_t parent = 1;
  uint32_t min    = parent;

  while (parent <= q->size / 2) {
    uint32_t lchild = 2 * parent;
    uint32_t rchild = 2 * parent + 1;

    if (q->items[parent].key > q->items[lchild].key) {
      min = lchild;
    }

    if (q->items[min].key > q->items[rchild].key) {
      min = rchild;
    }

    if (min == parent) {
      break;
    }

    swap(&q->items[parent], &q->items[min]);
    parent = min;
  }

  return 0;
}

void min_heap_push(MIN_HEAP* q, long key, void* data) {
  q->size++;
  q->items[q->size].key  = key;
  q->items[q->size].data = data;

  uint32_t child  = q->size;
  uint32_t parent = child / 2;
  while (child > 1) {
    if (q->items[parent].key <= q->items[child].key) {
      break;
    }

    swap(&q->items[parent], &q->items[child]);

    child  = parent;
    parent = child / 2;
  }

  if (q->size > q->capacity) {
    min_heap_pop(q, NULL);
  }
}

} // namespace memchecker

/*----------------------------------------------------------------------------*/

using namespace memchecker;

extern "C" void* malloc(size_t size) {
  if (!initted) {
    mem_checker_init();
  }

  if (inner_call) {
    return malloc_func(size);
  }
  inner_call = 1;

  void* addr[STACK_MAX_DEPTH];
  int depth = back_trace(addr, stack_depth);

  void* p = malloc_func(sizeof(MY_HEAD) + size);
  if (!p) {
    inner_call = 0;
    return p;
  }

  MY_HEAD* head = (MY_HEAD*)p;
  head->stack   = callstack_update(addr, depth, size);
  head->magic   = MY_MAGIC_ALLOC;
  head->size    = size;
  head->realptr = head;

  mc_log("malloc:%lu %p stack[%p]", size, head + 1, head->stack);
  save_ptr(head + 1, head->size, head->stack, MF_MALLOC);

  inner_call = 0;
  return (head + 1);
}

extern "C" void free(void* ptr) {
  if (!initted) {
    mem_checker_init();
  }

  if (!ptr) {
    return;
  }

  if (inner_call) {
    free_func(ptr);
    return;
  }

  inner_call = 1;

  MY_HEAD* head = (MY_HEAD*)(((char*)ptr) - sizeof(MY_HEAD));
  if (head->magic == MY_MAGIC_ALLOC) {
    head->magic  = MY_MAGIC_FREE;
    STACK* stack = head->stack;
    if (stack) {
      __sync_add_and_fetch(&stack->frees, 1);
      __sync_sub_and_fetch(&stack->size, head->size);
    }

    mc_log("free:%p stack[%p]", ptr, stack);
    save_ptr(ptr, head->size, head->stack, MF_FREE);

    free_func(head->realptr);
  } else {
    // bug if here ??
    //free_func(ptr);
    mc_log("free bad address %p", ptr);

    free_func(ptr);

    //abort();
  }

  inner_call = 0;
}

extern "C" void* calloc(size_t nmemb, size_t size) {
  if (!initted) {
    mem_checker_init();
  }

  if (inner_call) {
    return calloc_func(nmemb, size);
  }
  inner_call = 1;

  void* addr[STACK_MAX_DEPTH];
  int depth = back_trace(addr, stack_depth);

  size_t bytes = size * nmemb;
  void* p      = malloc_func(sizeof(MY_HEAD) + bytes);
  if (!p) {
    inner_call = 0;
    return p;
  }

  MY_HEAD* head = (MY_HEAD*)p;
  head->stack   = callstack_update(addr, depth, bytes);
  head->magic   = MY_MAGIC_ALLOC;
  head->size    = bytes;
  head->realptr = head;

  memset(head + 1, 0, bytes);

  mc_log("calloc:%lu %p stack[%p]", bytes, (head + 1), head->stack);

  save_ptr((head + 1), head->size, head->stack, MF_CALLOC);

  inner_call = 0;
  return (head + 1);
}

extern "C" void* realloc(void* ptr, size_t size) {
  if (!initted) {
    mem_checker_init();
  }

  if (inner_call) {
    return realloc_func(ptr, size);
  }
  inner_call = 1;

  void* addr[STACK_MAX_DEPTH];
  int depth = back_trace(addr, stack_depth);

  if (!ptr) {
    void* p = malloc_func(sizeof(MY_HEAD) + size);
    if (!p) {
      inner_call = 0;
      return p;
    }

    MY_HEAD* head = (MY_HEAD*)p;
    head->stack   = callstack_update(addr, depth, size);
    head->magic   = MY_MAGIC_ALLOC;
    head->size    = size;
    head->realptr = head;

    mc_log("realloc:%lu %p stack[%p]", size, (head + 1), head->stack);

    save_ptr((head + 1), head->size, head->stack, MF_REALLOC);

    inner_call = 0;
    return head + 1;
  }

  MY_HEAD* old_head = (MY_HEAD*)(((char*)ptr) - sizeof(MY_HEAD));
  if (old_head->magic != MY_MAGIC_ALLOC) {
    mc_log("realloc bad address %p", ptr);
    abort();
    // bug here 内存越界,错误的地址
    // realloc_func(ptr, size);
  }

  if (size == old_head->size) {
    mc_log("realloc with same size %p", ptr);
    inner_call = 0;
    return ptr;
  }

  /*
     * If size is 0 and ptr is not a null pointer, the object pointed to  is  freed
     */
  if (size == 0) {
    old_head->magic = MY_MAGIC_FREE;
    STACK* stack    = old_head->stack;
    if (stack) {
      __sync_add_and_fetch(&stack->frees, 1);
      __sync_sub_and_fetch(&stack->size, old_head->size);
    }

    free_func(old_head->realptr);

    mc_log("realloc with size = 0");

    save_ptr(ptr, old_head->size, old_head->stack, MF_REALLOC_FREE_ZERO);

    inner_call = 0;
    return NULL;
  }

  // realloc可能重新分配内存,分配成功会释放ptr,
  old_head->magic  = MY_MAGIC_FREE;
  size_t old_size  = old_head->size;
  STACK* old_stack = old_head->stack;

  void* p = realloc_func(old_head->realptr, size + sizeof(MY_HEAD));
  if (!p) {
    inner_call      = 0;
    old_head->magic = MY_MAGIC_ALLOC;
    return p;
  }

  MY_HEAD* head = (MY_HEAD*)p;
  head->size    = size;
  head->magic   = MY_MAGIC_ALLOC;
  head->realptr = head;

  if (head->stack) {
    __sync_add_and_fetch(&head->stack->frees, 1);
    __sync_sub_and_fetch(&head->stack->size, old_size);
  }

  head->stack = callstack_update(addr, depth, size);

  mc_log("realloc:%lu %p stack[%p]", size, (head + 1), head->stack);

  save_ptr((old_head + 1), old_size, old_stack, MF_REALLOC_FREE_OLD);
  save_ptr((head + 1), head->size, head->stack, MF_REALLOC);

  inner_call = 0;

  return head + 1;
}

extern "C" void* memalign(size_t boundary, size_t size) {
  if (!initted) {
    mem_checker_init();
  }

  if (inner_call) {
    return memalign_func(boundary, size);
  }

  inner_call = 1;

  void* addr[STACK_MAX_DEPTH];
  int depth = back_trace(addr, stack_depth);

  size_t head_block_size = (sizeof(MY_HEAD) + boundary - 1) & ~(boundary - 1);
  void* base             = memalign_func(boundary, head_block_size + size);
  if (!base) {
    inner_call = 0;
    return NULL;
  }

  MY_HEAD* head = (MY_HEAD*)(((char*)base + head_block_size) - sizeof(MY_HEAD));
  head->magic   = MY_MAGIC_ALLOC;
  head->size    = size;
  head->realptr = base;
  head->stack   = callstack_update(addr, depth, size);

  mc_log("memalign:%lu %p stack[%p]", size, head + 1, head->stack);

  save_ptr((head + 1), head->size, head->stack, MF_MEMALIGN);

  inner_call = 0;

  return head + 1;
}

extern "C" void* __libc_memalign(size_t boundary, size_t size) {
  return memalign(boundary, size);
}

extern "C" int posix_memalign(void** memptr, size_t alignment, size_t size) {
  void* p = memalign(alignment, size);
  if (p) {
    *memptr = p;
    return 0;
  }
  return -1;
}

extern "C" void* valloc(size_t size) {
  return memalign(sysconf(_SC_PAGESIZE), size);
}

extern "C" void* mmap(void* addr, size_t len, int prot, int flags, int fildes, off_t off) {
  if (!initted) {
    mem_checker_init();
  }

  if (inner_call) {
    return mmap_func(addr, len, prot, flags, fildes, off);
  }

  inner_call = 1;

  void* stack_addr[STACK_MAX_DEPTH];
  int depth = back_trace(stack_addr, stack_depth);

  void* p = mmap_func(addr, len, prot, flags, fildes, off);
  if (!p) {
    inner_call = 0;
    return p;
  }

  MAP_AREA* mma = (MAP_AREA*)malloc_func(sizeof(MAP_AREA));
  mma->start    = (unsigned long)p;
  mma->end      = (unsigned long)p + len;
  mma->stack    = callstack_update(stack_addr, depth, len);
  mma->ma_next  = NULL;
  reg_mm_area(mma);

  mc_log("mmap:%lu %p stack[%p]", len, p, mma->stack);

  save_ptr(p, len, mma->stack, MF_MMAP);

  inner_call = 0;

  return p;
}

extern "C" int munmap(void* addr, size_t len) {
  if (!initted) {
    mem_checker_init();
  }

  if (inner_call) {
    return munmap_func(addr, len);
  }

  inner_call = 1;

  int s = munmap_func(addr, len);
  if (!s) {
    unreg_mm_area((unsigned long)addr, len);

    save_ptr(addr, len, NULL, MF_MUNMAP);

    mc_log("munmap:%lu %p", len, addr);
  }

  inner_call = 0;

  return s;
}
