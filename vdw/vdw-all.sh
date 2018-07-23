#!/bin/bash

echo "vdw(3,3) = 9"
./vdw 2 3  3   8 >data/vdw-3-03-008.out
./vdw 2 3  3   9 >data/vdw-3-03-009.out

echo "vdw(3,4) = 18"
./vdw 2 3  4  17 >data/vdw-3-04-017.out
./vdw 2 3  4  18 >data/vdw-3-04-018.out

echo "vdw(3,5) = 22"
./vdw 2 3  5  21 >data/vdw-3-05-021.out
./vdw 2 3  5  22 >data/vdw-3-05-022.out

echo "vdw(3,6) = 32"
./vdw 2 3  6  31 >data/vdw-3-06-031.out
./vdw 2 3  6  32 >data/vdw-3-06-032.out

echo "vdw(3,7) = 46"
./vdw 2 3  7  45 >data/vdw-3-07-045.out
./vdw 2 3  7  46 >data/vdw-3-07-046.out

echo "vdw(3,8) = 58"
./vdw 2 3  8  57 >data/vdw-3-08-057.out
./vdw 2 3  8  58 >data/vdw-3-08-058.out

echo "vdw(3,9) = 77"
./vdw 2 3  9  76 >data/vdw-3-09-076.out
./vdw 2 3  9  77 >data/vdw-3-09-077.out

echo "vdw(3,10) = 97"
./vdw 2 3 10  96 >data/vdw-3-10-096.out
./vdw 2 3 10  97 >data/vdw-3-10-097.out

echo "vdw(3,11) = 114"
./vdw 2 3 11 113 >data/vdw-3-11-113.out
./vdw 2 3 11 114 >data/vdw-3-11-114.out

echo "vdw(3,12) = 135"
./vdw 2 3 12 134 >data/vdw-3-12-134.out
./vdw 2 3 12 135 >data/vdw-3-12-135.out

echo "vdw(4,4) = 35"
./vdw 2 4  4  34 >data/vdw-4-04-034.out
./vdw 2 4  4  35 >data/vdw-4-04-035.out

echo "vdw(4,5) = 55"
./vdw 2 4  5  54 >data/vdw-4-05-054.out
./vdw 2 4  5  55 >data/vdw-4-05-055.out

echo "vdw(4,6) = 73"
./vdw 2 4  6  72 >data/vdw-4-06-072.out
./vdw 2 4  6  73 >data/vdw-4-06-073.out

echo "vdw(5,5) = 178"
./vdw 2 5  5 177 >data/vdw-5-05-177.out
./vdw 2 5  5 178 >data/vdw-5-05-178.out

