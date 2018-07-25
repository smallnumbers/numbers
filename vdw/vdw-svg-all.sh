#!/bin/bash

render () {
	echo $1
	./vdw-svg.py < data/vdw-$1.out > img/vdw-$1.svg
}

render 3-03-008
render 3-04-017
render 3-05-021
render 3-06-031
render 3-07-045
render 3-08-057
render 3-09-076
render 3-10-096
render 3-11-113
render 3-12-134
render 3-13-159
render 4-04-034
render 4-05-054
render 4-06-072
render 4-07-108
render 5-05-177

render 2-3-3-13
render 2-3-4-20
render 2-3-5-31
render 2-3-6-39
render 2-3-7-54
render 2-3-8-71
render 2-3-9-89
render 2-3-10-107
render 2-3-11-128
render 2-4-4-39
render 2-4-5-70
render 2-4-6-82
render 3-3-3-26
render 3-3-4-50

render 2-2-3-3-16
render 2-2-3-4-24
render 2-2-3-5-42
render 2-2-3-6-47
render 2-2-3-5-42
render 2-2-3-6-47
render 2-2-3-7-64
render 2-2-3-8-82
render 2-2-3-9-98
render 2-2-4-4-52
render 2-3-3-3-39
render 2-3-3-4-59

render 2-2-2-3-3-19
render 2-2-2-3-4-28
render 2-2-2-3-5-43
render 2-2-2-3-6-55
render 2-2-2-4-4-53
render 2-2-3-3-3-40

