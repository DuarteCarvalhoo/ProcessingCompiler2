# ProcessingCompiler2

flex hello.l
bison -dy hello.y

gcc arvoreAST.c TabelaDeSimbolo.c lex.yy.c y.tab.c -o testOpen -lopengl32 -lglew32 -lfreeglut -lglu32
