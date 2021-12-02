Filter.vo : Filter.v FuncDef.vo
	coqc Filter.v

FuncDef.vo : FuncDef.v Sequences.vo CPO.vo CoList.vo Functional.vo
	coqc FuncDef.v

Functional.vo : Functional.v CoList.vo TypeDecl.vo
	coqc Functional.v

TypeDecl.vo : TypeDecl.v
	coqc TypeDecl.v

CoList.vo : CoList.v CPO.vo Sequences.vo WfInf.vo
	coqc CoList.v

WfInf.vo : WfInf.v
	coqc WfInf.v

CPO.vo : CPO.v Sequences.vo
	coqc CPO.v

Sequences.vo : Sequences.v
	coqc Sequences.v

clean :
	rm *.vo *.vok *.vos *.glob
