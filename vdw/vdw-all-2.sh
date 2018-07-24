#!/bin/bash

verify () {
	k1=$1
	k2=$2
	n=$3
	nm=$(($n - 1))
	echo "vdw($k1,$k2) = $n"
	./vdw 2 $k1 $k2 $nm >data/vdw-$k1-$k2-$nm.out
	./vdw 2 $k1 $k2 $n >data/vdw-$k1-$k2-$n.out
}

# Commented rows have been verified

#verify 3  3   9
#verify 3  4  18
#verify 3  5  22
#verify 3  6  32
#verify 4  4  35
#verify 3  7  46
#verify 4  5  55
#verify 3  8  58
#verify 4  6  73
#verify 3  9  77
#verify 3 10  97
#verify 4  7 109
#verify 3 11 114
#verify 3 12 135
#verify 4  8 146
#verify 3 13 160
#verify 5  5 178

verify 3 14 186
verify 3 15 186
verify 5  6 206
verify 3 16 238
verify 5  7 260
verify 3 17 279
verify 4  9 309
verify 3 18 312
verify 3 19 349
verify 6 6 1132
