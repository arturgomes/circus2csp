#!/bin/bash
ghc -o moduledeps ModuleDeps.hs
ls ../*.lhs > _lhs.log
ack -w import ../*.lhs > _import.log
./moduledeps