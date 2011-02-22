#!/bin/sh

for i in test*.lml ; do 
    echo "RUNNING:     $i" ;
    ../../liml $i -main Test ; 
done
