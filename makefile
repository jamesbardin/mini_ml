all: eva exp min

eva : evaluation.ml
	ocamlbuild -use-ocamlfind evaluation.byte
	
exp : expr.ml
	ocamlbuild -use-ocamlfind expr.byte
	
min : miniml.ml
	ocamlbuild -use-ocamlfind miniml.byte


	
clean : 
	rm -r _build
	rm *.byte
