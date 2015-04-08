default:
	bison -d holt_adam_postfix.ypp
	flex holt_adam_postfix.l
	g++ -o mycalc holt_adam_postfix.tab.cpp lex.yy.c
