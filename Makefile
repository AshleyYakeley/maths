default: build

build:
	coqc -I `pwd` -R theory Ashley theory/Logic.v
	coqc -I `pwd` -R theory Ashley theory/Set.v
	coqc -I `pwd` -R theory Ashley theory/Topology.v
	coqc -I `pwd` -R theory Ashley theory/Group.v
clean:
	rm -f theory/*.v.d theory/*.vo theory/*.glob theory/makefile
