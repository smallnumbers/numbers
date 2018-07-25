#!/bin/bash

verify () {
	k1=$1
	k2=$2
	k3=$3
	k4=$4
	k5=$5
	n=$6
	nm=$(($n - 1))
	echo "vdw($k1,$k2,$k3,$k4,$k5) = $n"
	./vdw 5 $k1 $k2 $k3 $k4 $k5 $nm >data/vdw-$k1-$k2-$k3-$k4-$k5-$nm.out
	./vdw 5 $k1 $k2 $k3 $k4 $k5 $n >data/vdw-$k1-$k2-$k3-$k4-$k5-$n.out
}

#verify 2 2 2 3 3  20
#verify 2 2 2 3 4  29
#verify 2 2 3 3 3  41
#verify 2 2 2 4 4  54
#verify 2 2 2 3 6  56
verify 2 2 3 3 4  63
verify 2 2 2 3 7  72
verify 2 2 2 4 5  79
verify 2 2 2 3 8  88
verify 2 2 2 4 6 101
verify 2 2 2 3 9 107

