#!/bin/sh

ocamlbuild -use-ocamlfind -libs graph -pkgs str -cflags -I,/Users/bingo/Projects/courseworks/EECS322/ocamlgraph-1.8.7 -lflags -g,-I,/Users/bingo/Projects/courseworks/EECS322/ocamlgraph-1.8.7 graph_color_exec.native
