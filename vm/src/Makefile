p:
	coqc Utils
	coqc Common
	coqc C
	coqc CU
	coqc C_to_CU
	coqc FB
	coqc CU_to_FB
	coqc CCP
	coqc FB_to_CCP
	coqc D
	coqc CCP_to_D
	coqc VM
	coqc D_to_VM
	coqdoc -t "" -g --toc --html --utf8 Utils.v Common.v C.v CU.v C_to_CU.v FB.v CU_to_FB.v CCP.v FB_to_CCP.v D.v CCP_to_D.v VM.v D_to_VM.v
	mv *.html doc
	mv *.css doc
