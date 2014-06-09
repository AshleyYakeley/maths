default: build

build:
	coqc -I `pwd` -R theory Ashley theory/Axioms.v
	coqc -I `pwd` -R theory Ashley theory/Proposition.v
	coqc -I `pwd` -R theory Ashley theory/Logic.v
	coqc -I `pwd` -R theory Ashley theory/Logic/Bool.v
	coqc -I `pwd` -R theory Ashley theory/Logic/Prop.v
	coqc -I `pwd` -R theory Ashley theory/Logic/Unary.v
	coqc -I `pwd` -R theory Ashley theory/Logic/Ternary.v
	coqc -I `pwd` -R theory Ashley theory/Set.v
	coqc -I `pwd` -R theory Ashley theory/Function.v
	coqc -I `pwd` -R theory Ashley theory/Category.v
	coqc -I `pwd` -R theory Ashley theory/SetFunction.v
	coqc -I `pwd` -R theory Ashley theory/Topology.v
	coqc -I `pwd` -R theory Ashley theory/Group.v
clean:
	rm -f theory/makefile theory/*.v.d theory/*.vo theory/*.glob theory/*/*.v.d theory/*/*.vo theory/*/*.glob
