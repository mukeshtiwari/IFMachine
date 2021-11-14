#!/bin/bash

for i in $(seq 100)
do
 # $RANDOM generates values in the range 0..32767
 # see https://tldp.org/LDP/abs/html/randomvar.html
 # random delay of up to four seconds to simulate misbehaving clients
 # use & so each iteration of the loop doesn't block the following one   
 ((sleep $(expr $RANDOM / 8192); echo "$i $RANDOM") |  nc 127.0.0.1 3000 ) &
done
