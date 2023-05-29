:- module(_,_,[assertions,regtypes]).
:- doc(hide, author_data/4).
author_data('Moreno','Ferreiro','Alejandro','A180413').

:- doc(title, "Aut@'{o}matas Celulares Reversibles").

:- doc(author, "Alejandro Moreno Ferreiro, A180413").

:- doc(module, " Documentaci@'{o}n acerca de los predicados realizados.

").

:- doc(hide, color/1).
:- doc(hide, rule/5).


color(o).
color(x).

rule(o,o,o,_,o). % regla nula
rule(x,o,o,r(A,_,_,_,_,_,_),A) :- 
    color(A).
rule(o,x,o,r(_,B,_,_,_,_,_),B) :- 
    color(B).
rule(o,o,x,r(_,_,C,_,_,_,_),C) :- 
    color(C).
rule(x,o,x,r(_,_,_,D,_,_,_),D) :- 
    color(D).
rule(x,x,o,r(_,_,_,_,E,_,_),E) :- 
    color(E).
rule(o,x,x,r(_,_,_,_,_,F,_),F) :- 
    color(F).
rule(x,x,x,r(_,_,_,_,_,_,G),G) :- 
    color(G).

:- pred apply_rule(List,Rule,Res)
    #" Predicado auxiliar que aplica las reglas proporcionadas dado un estado inicial y genera una lista con el estado resultante de aplicar la regla sucesivamente. Argumentos: [X,Y,Z|R]: Lista con el estado inicial con al menos 3 elementos. Rule: Regla a aplicar. @item [Res|Resto]: Lista con el resultado, el primer elemento viene de aplicar una regla y el resto de hacer la llamada recusriva con la lista del primer argumento, quitando el primer elemento. La recursividad acaba cuando la lista tiene 2 o menos elementos devolviendo como resultado en el tercer argumento la lista vacía.@includedef{apply_rule/3}".
apply_rule([X,Y,Z|R],Rule,[Res|Resto]) :-
    rule(X,Y,Z,Rule,Res),
    apply_rule([Y,Z|R],Rule,Resto).

apply_rule([],_,[]).
apply_rule([_],_,[]).
apply_rule([_,_],_,[]).

:- pred own_append(List,List,Res)
    #"Implementaci@'{o}n propia del append, que concatena dos listas. @includedef{own_append/3}".
own_append([],W,W).
own_append([X|V],W,[X|R]) :-
    own_append(V,W,R).

:- pred cells(List,Rule,Result)
    #" Predicado cells, Se utiliza el own_append para introducir un 0 al principio de la lista y un 0 al final cuando tengas el resultado. Comprueba que el primer y el @'{u}ltimo elemento de la lista es 0 y aplica la regla para generar el estado final. Argumentos: L: Lista con el estado inicial. @item Rule: Regla a aplicar. [o|R]: Lista resultado de aplicar la regla con el predicado aply_rule. @includedef{cells/3}".
cells(L,Rule,[o|R]):-
    first(L,o),
    ultimo(L,o),
    own_append(L,[o],LL),
    apply_rule([o|LL],Rule,RR),
    own_append(RR,[o],R).

:- pred first(List,N) #"Compara el primer valor de una lista dada. @includedef{first/2}".
first([X|_],X).
:-pred ultimo(List,N) #"Compara el @'{u}ltimo valor de la lista @includedef{ultimo/2}".
ultimo([X],X).
ultimo([_|L],X):-
    ultimo(L,X).




:- pred evol(Sucesor,Rule,EF) #" Aplica N paso de evolucion desde un estado dado usando el predicado cells sucesivamente. Argumentos: Numero de pasos. Regla a aplicar. Estado final que se alcanza. @includedef{evol/3}".
evol(0,_,[o,x,o]).
evol(s(N),Rule,Cells) :- 
    evol(N, Rule, EI),
    cells(EI,Rule,Cells).

:- pred steps(List,Sucesor) #" Número de pasos necesarios para llegar un estado a partir de una configuraci@'{o}n inicial de tres @'{e}lulas. Como en cada paso se añaden dos c@'{e}lulas al estado anterior, se construye la lista de 3,5,7 miembros. Argumentos: Estado que se alcanza tras N pasos. Número de pasos. @includedef{steps/2}".
steps([_,_,_],0).   
steps([_,_|L],s(N)) :- 
    steps(L,N).

:- pred ruleset(Rule,FS) #"Descubre si un estado final es alcanzable y con que regla. Argumentos: Regla a aplicar. Estado final. @includedef{ruleset/2}".
ruleset(Rule,FS) :- 
    steps(FS,N), 
    evol(N,Rule,FS).

%Test

:- test apply_rule(List,Rule,Res) : (List = [o,x,x,x,o,o,o,x,o,o,x,x,o,x,x,x,x,o,x,x,o] , Rule = r(x,x,o,x,o,x,o)) => (Res = [x,o,o,x,o,o,x,x,o,x,o,x,x,o,o,o,x,x,o]) + not_fails #"Test apply_rule1".
:- test apply_rule(List,Rule,Res) : (List = [o,x,o,o,o,x,o] , Rule = r(x,x,o,x,o,o,x) ) => (Res = [x,x,o,o,x]) + not_fails #"Test apply_rule2".
:- test apply_rule(List,Rule,Res) : (List = [o,x,o], Rule = r(x,x,x,o,o,x,o)) => (Res = [x]) + not_fails #"Test apply_rule3".

:- test cells(List,Rule,Result) : (List = [o,x,o], Rule = r(x,x,o,x,x,o,x)) => (Res = [o,o,x,x,o]) + not_fails #"Test cells1".
:- test cells(List,Rule,Result) : (List = [o,x,o,o,o,o,x,x,x,o,o,x,o,x,o], Rule = r(x,o,o,x,x,x,o)) => (Res = [o,o,o,x,o,o,o,x,o,x,x,o,o,x,o,x,o]) + not_fails #"Test cells2".
:- test cells(List,Rule,Result) : (List = [o,x,x,x,o,o,o,x,o,o,x,x,o,x,x,x,x,o,x,x,o], Rule = r(x,x,o,x,o,o,x)) => (Res = [o,o,o,x,o,x,o,o,x,x,o,o,o,x,o,x,x,o,x,o,o,x,o]) + not_fails #"Test cells3".


:- test evol(Sucesor,Rule,EF) : (Sucesor = s(s(s(s(s(s(0)))))), Rule = r(x,x,o,x,x,o,x)) => (EF = [o,o,o,o,o,o,o,o,o,o,o,o,x,x,o]) + not_fails #"Test evol1".
:- test evol(Sucesor,Rule,EF) : (Sucesor = s(s(s(s(s(s(0)))))), Rule = r(x,o,o,x,x,x,o)) => (EF = [o,o,o,o,o,o,o,o,o,o,o,o,o,x,o]) + not_fails#"Test evol2".
:- test evol(Sucesor,Rule,EF) : (Sucesor = s(0), Rule = r(o,x,o,x,x,x,o)) => (EF = [o,o,x,o,o]) + not_fails#"Test evol3".

:- test steps(List, Sucesor) : (List = [o,o,o,o,o,o,o,o,o,o,o,o,x,x,o], Sucesor = N) => (N = s(s(s(s(s(s(0))))))) + not_fails #"Test steps1".
:- test steps(List, Sucesor) : (List = [o,x,x,x,o,o,o,x,o,o,x,x,o,x,x,x,x,o,x,x,o], Sucesor = N) => (N = s(s(s(s(s(s(s(s(s(0))))))))) ) + not_fails #"Test steps2".
:- test steps(List, Sucesor) : (List = [o,o,x,x,o], Sucesor = N) => (N = s(0)) + not_fails #"Test steps3".

:- test ruleset(Rule, FS) : (Rule = RuleSet, FS = [o,x,x,o,o,x,o,o,o,o,x,o,o,x,o]) => (RuleSet = r(x,x,x,o,o,x,o)) + not_fails #"Test ruleset1".
:- test ruleset(Rule, FS) : (Rule = RuleSet, FS = [o,x,x,o,o,x,o,o,o,o,x,o,x,x,o]) + fails #"Test ruleset2".

















