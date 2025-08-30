# CYaRonC

CYaRon! language compiler to LLVM IR.

## Usage

Build:
```bash
mkdir -p build && cd build
cmake -DCMAKE_BUILD_TYPE=Release ..
make
```

Usage:

Compile to LLVM IR:
```bash
./cyaronc input.cyaron output.ll
```

Execute:
```bash
# run the LLVM IR directly
lli output.ll
# or compile to executable file and run it
clang output.ll -o output
./output
```

## Test
`lli` is required to be in the PATH.
```
python3 test/run_tests.py
```

## Reference

<https://www.luogu.com.cn/problem/P3695>

```
{ vars
    chika:int
    you:int
    ruby:array[int, 1..2]
    i:int
}
# 以上变量默认值均为0
# 变量名只可是英文字母。

# yosoro语句可以输出一个数字，随后跟一个空格。
:yosoro 2
# 输出2和一个空格(以下不再提到空格)。

# set语句可以为变量赋值。
# 运算符只支持加减号即可。
:set chika, 1
:set you, 2
:yosoro chika + you
# 上一条语句将输出3

# 以下的判断语句均使用以下的格式：
# 操作符，表达式，表达式
# 例如eq, a, 1即C语言中 a==1
# 所有操作符包括: lt: < gt: > le: <= ge: >= eq: == neq: !=

# 日本来的CYaRon三人没法正确地发出if这个音，因此她们就改成了ihu。
{ ihu eq, chika, 1
    :set you, 3
    :yosoro 1
}
# 输出1
# 以上是ihu语句，无需支持else。

# hor语句同理，
# for i=1 to you如下
{ hor i, 1, you
    :yosoro i
}
# 输出1 2 3

# 如下是while和数组的使用方法。
:set i, 1
{ while le, i, 2
    :yosoro i
    :set ruby[i], i+1
    :yosoro ruby[i]
    :set i, i+1
}
# 输出1 2 2 3

# 数组不会出现嵌套，即只会有a[i]、a[i+2]而不会有类似于a[i+b[i]]这样的。

# CYaRon语的最后一行，一定是一个换行。
```