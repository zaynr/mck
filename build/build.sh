
export build_dir=`dirname $0`
export root_dir=`cd ${build_dir}/..; pwd`
export output_dir="${root_dir}/output"

function prepare()
{
  if [ -d ${output_dir} ]; then
    rm -rf ${output_dir}
  fi

  mkdir -p ${output_dir}
}

function compile()
{
  prepare

  pushd ${output_dir}
  cmake ..
  make clean
  make -j8
  popd
}

function main()
{
  compile
}

main
