#!/bin/bash

verify () {
	k1=$1
	k2=$2
	k3=$3
	n=$4
	nm=$(($n - 1))
	echo "vdw($k1,$k2,$k3) = $n"
	time ./vdw 3 $k1 $k2 $k3 $nm >&data/vdw-$k1-$k2-$k3-$nm.out &
	time ./vdw 3 $k1 $k2 $k3 $n >&data/vdw-$k1-$k2-$k3-$n.out
}

#verify 2 3 3 14
#verify 2 3 4 21
#verify 3 3 3 27
#verify 2 3 5 32
#verify 2 3 6 40
#verify 2 4 4 40
#verify 3 3 4 51
#verify 2 3 7 55
#verify 2 4 5 71
#verify 2 3 8 72
#verify 3 3 5 80
#verify 2 4 6 83

verify 3 4 4 89
verify 2 3 9 90
verify 3 3 6 107
verify 2 3 10 108
verify 2 4 7 119
verify 2 3 11 129
verify 2 3 12 150
verify 2 4 8 157
verify 2 3 13 171
verify 2 5 5 180
verify 2 3 14 202
verify 2 5 6 246
verify 4 4 4 293
