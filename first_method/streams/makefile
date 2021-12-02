Fibo.vo : Fibo.v FunctionDefinition.vo
	coqc Fibo.v

Filter.vo : Filter.v FunctionDefinition.vo
	coqc Filter.v

FunctionDefinition.vo : FunctionDefinition.v Sequences.vo CPO.vo Flat.vo MyStreams.vo Functional.vo
	coqc FunctionDefinition.v

Functional.vo : Functional.v MyStreams.vo TypeDecl.vo
	coqc Functional.v

TypeDecl.vo : TypeDecl.v
	coqc TypeDecl.v

MyStreams.vo : MyStreams.v Flat.vo CPO.vo Sequences.vo
	coqc MyStreams.v

Flat.vo : Flat.v CPO.vo Sequences.vo
	coqc Flat.v

CPO.vo : CPO.v Sequences.vo
	coqc CPO.v

Sequences.vo : Sequences.v
	coqc Sequences.v



clean :
	rm *.vo *.vok *.vos *.glob
