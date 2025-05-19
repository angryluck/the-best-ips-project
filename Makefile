all:
	dotnet build -v n Fasto

clean:
	rm -rf Fasto/bin Fasto/obj
	rm -f Fasto/Parser.fs Fasto/Parser.fsi Fasto/Parser.fsyacc.output Fasto/Lexer.fs Fasto/Lexer.fsi tests/*.asm
