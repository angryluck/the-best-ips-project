all:
	dotnet build -v n Fasto

test:   
	make clean
	make
	bin/runtests.sh

scratch:
	bin/compilerun.sh scratch.fo

clean:
	rm -rf Fasto/bin Fasto/obj
	rm -f Fasto/Parser.fs Fasto/Parser.fsi Fasto/Parser.fsyacc.output Fasto/Lexer.fs Fasto/Lexer.fsi tests/*.asm
