#!/bin/sh

for i in test*.lml ; do 
    echo "RUNNING:     $i" ;
    ../../limlc $i -root Test ; 
done
