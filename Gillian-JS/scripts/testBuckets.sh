#!/bin/bash

bin="$1"

foldername=${PWD##*/}
if [ "$foldername" != "environment" ]
then
	cd environment
fi

./testBucketsFolder.sh arrays $bin
sleep 5
./testBucketsFolder.sh bag $bin
sleep 5
./testBucketsFolder.sh bstree $bin
sleep 5
./testBucketsFolder.sh dictionary $bin
sleep 5
./testBucketsFolder.sh heap $bin
sleep 5
./testBucketsFolder.sh linkedlist $bin
./testBucketsFolder.sh linkedlist/bug $bin
sleep 5
./testBucketsFolder.sh multidictionary $bin
./testBucketsFolder.sh multidictionary/bug $bin
sleep 5
./testBucketsFolder.sh queue $bin
sleep 5
./testBucketsFolder.sh priorityqueue $bin
sleep 5
./testBucketsFolder.sh set $bin
sleep 5
./testBucketsFolder.sh stack $bin