Mirror.vo: Mirror.v Tree.vo FuncDef.vo
	coqc Mirror.v

Tree.vo : Tree.v FiniteOrderMeasure.vo
	coqc Tree.v

FuncDef.vo : FuncDef.v CPO.vo
	coqc FuncDef.v

CPO.vo : CPO.v FiniteOrderMeasure.vo Sequences.vo EqvClasses.vo
	coqc CPO.v

EqvClasses.vo : EqvClasses.v 
	coqc EqvClasses.v

FiniteOrderMeasure.vo : FiniteOrderMeasure.v
	coqc FiniteOrderMeasure.v

Sequences.vo : Sequences.v WfInf.vo
	coqc Sequences.v

WfInf.vo : WfInf.v
	coqc WfInf.v


clean :
	rm *.vo *.vok *.vos *.glob
