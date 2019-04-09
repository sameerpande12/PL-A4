all:
	ocamlc -c a0.mli
	ocamlc -c a0.ml
	ocamlc -c a1.mli
	ocamlc -c a1.ml
	ocamllex a2.mll
	ocamlyacc a3.mly
	ocamlc -c a3.mli
	ocamlc -c a3.ml
	ocamlc -c a2.ml
	ocamlc -c a4.mli
	ocamlc -c a4.ml

clean:
	rm  *.cmo *.cmi a3.mli  a2.ml a3.ml
