# 内存检测器

**仅支持 GNU**

该工程提供通过 LD_PRELOAD 来 hook 住 glibc 里的 malloc、free、relloc 等内存分配动作，记录所有代码里的内存分配、回收次数，从而可以监测到代码里的内存泄漏
