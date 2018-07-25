#!/bin/bash

verify () {
	k1=$1
	k2=$2
	k3=$3
	k4=$4
	n=$5
	nm=$(($n - 1))
	echo "vdw($k1,$k2,$k3,$k4) = $n"
	./vdw 4 $k1 $k2 $k3 $k4 $nm >data/vdw-$k1-$k2-$k3-$k4-$nm.out
	./vdw 4 $k1 $k2 $k3 $k4 $n >data/vdw-$k1-$k2-$k3-$k4-$n.out
}

#verify 2 2 3 3 17
#verify 2 2 3 4 25
#verify 2 2 3 5 43
#verify 2 2 3 6 48
#verify 2 2 3 7 65
#verify 2 2 3 8 83
#verify 2 2 3 9 99

verify 2 3 3 3 40
verify 2 2 4 4 53
verify 2 3 3 4 60
verify 2 2 4 5 75
verify 3 3 3 3 76
verify 2 3 3 5 86
verify 2 2 4 6 93
verify 2 2 3 10 119
verify 2 2 3 11 141

