:- module(code,_,[classic ,assertions, regtypes]).
:- doc(hide, author_data/4).
author_data('Moreno','Ferreiro','Alejandro','A180413').

:- doc(title, "Recorridos de valor m@'{i}nimo en tableros").

:- doc(author, "Alejandro Moreno Ferreiro, A180413").

:- doc(module, " Documentaci@'{o}n acerca de los predicados realizados").

:- pred efectuar_movimiento(Pos,D,Pos2)
    #"Predicado que dada una posici@'{o}n y un direcci@'{o}n, efectua un movimiento en el tablero. El movimiento se efectua sumando o restando 1 a la/s coordenada/s seg. @includedef{efectuar_movimiento/3}".
efectuar_movimiento(pos(X,Y), e, pos(X,B)):- B is Y+1. %Este
efectuar_movimiento(pos(X,Y), o, pos(X,B)):- B is Y-1. %Oeste
efectuar_movimiento(pos(X,Y), s, pos(A,Y)):- A is X+1. %Norte
efectuar_movimiento(pos(X,Y), n, pos(A,Y)):- A is X-1. %Sur
efectuar_movimiento(pos(X,Y), no, pos(A,B)):- A is X-1, B is Y-1. %Noroeste
efectuar_movimiento(pos(X,Y), ne, pos(A,B)):- A is X-1, B is Y+1. %Noreste
efectuar_movimiento(pos(X,Y), so, pos(A,B)):- A is X+1, B is Y-1. %Suroeste
efectuar_movimiento(pos(X,Y), se, pos(A,B)):- A is X+1, B is Y+1. %Sureste

:- pred posicion_valida(N,Pos)
    #"Predicado que dada una posci@'{o}n y un N que define el tama@~{n}o del tablero, indica si esa posici@'{o}n dada forma parte del tablero. @includedef{posicion_valida/2}".
posicion_valida(N, pos(X, Y)) :-
    between(1, N, X),
    between(1, N, Y).

:- pred movimiento_valido(N,Pos,Dir)
    #"Predicado que recibe un N que define el tama@~{n}o del tablero, una posci@'{o}n y una direcci@'{o}n, indica que la posici@'{o}n resultante de realizar el movimiento es v@'{a}lida. @includedef{movimiento_valido/3}".
movimiento_valido(N, Pos, Dir) :-
    efectuar_movimiento(Pos, Dir, Pos2),
    posicion_valida(N, Pos2).

:- pred select_cell(Pos,Op,Board,NewBoard)
    #"Predicado que recibe una posci@'{o}n, una operaci@'{o}n, y un tablero. Extrae una Pos de la lista Board obteniendo NewBoard (sin dicha celda) y unificando Op con la operaci@'{o}n asociada a la respectiva celda.Utiliza member para sacar la celda que se desea eleminar del tablero, y con el select genera el nuevo tablero sin dicha celda. @includedef{select_cell/4}".
select_cell(Pos, Op, Board, NewBoard) :-
    member(cell(Pos, Op), Board),
    select(cell(Pos, Op), Board, NewBoard).

:- pred select_dir(D,Dirs,NewDirs)
    #"Predicado que recibe una direcci@'{o}n como argumento y extrae una direcci@'{o}n Dir de las permitidas en Dirs , obteniendo en NewDirs la lista de direcciones permitidas que restan. Utiliza el select, para sacar la direcci@'{o}n dado de la lista de direcciones permitidas y genera una nueva. Se utiliza un condicional que evalua: Si solo se puede mover una vez, la lista de direciones disponibles es la generada por select y sino se resta un movimiento y se actualiza la lista de direcciones permitidas. @includedef{select_dir/3}".
select_dir(D, Dirs, NewDirs) :-
    select(dir(D,X), Dirs, Resto),
    (X==1 -> NewDirs=Resto;
            Actualizado is X-1,
            NewDirs = [dir(D,Actualizado) | Resto]).

:- pred aplicar_op(Op,Valor,ValorResultado)
    #"Predicado que dada una operaci@'{o}n, aplica la operaci@'{o}n correspondiente al Valor, generando un nuevo valor. @includedef{aplicar_op/3}".
aplicar_op(op(+, Operando), Valor, Valor2) :-
    Valor2 is Valor + Operando.

aplicar_op(op(-, Operando), Valor, Valor2) :-
    Valor2 is Valor - Operando.

aplicar_op(op(*, Operando), Valor, Valor2) :-
    Valor2 is Valor * Operando.

aplicar_op(op(//, Operando), Valor, Valor2) :-
    Valor2 is Valor // Operando.



:- pred generar_recorridoAux(Pos,N,Board,DireccionesPermitidas,Recorrido, Valor, V)
    #"Predicado que utiliza el predicado select_dir para seleccionar una direcci@'{o}n (Dir) de la lista de direcciones permitidas (DireccionesPermitidas) y devuelve la lista de direcciones restantes (Dirs). Verifica si el movimiento (Dir) es v@'{a}lido utilizando el predicado movimiento_valido con los argumentos N, Ipos y Di. Utiliza el predicado efectuar_movimiento para obtener la nueva posici@'{o}n (Npos) a partir de la posici@'{o}n actual (Ipos) y la irecci@'{o}n (Dir). Utiliza el predicado select_cell para seleccionar una celda (Op) en el tablero (Board) bas@'{a}ndose en la nueva posici@'{o}n (Npos) y devuelve el nuevo tablero (NBoard). Aplica la operaci@´{o}n (Op) a los valores actuales (Valor) y obtiene el nuevo valor (NuevoValor) utilizando el predicado aplicar_op. Llama recursivamente al predicado generar_recorridoAux con la nueva posici@'{o}n (Npos), el mismo tamaño del recorrido (N), el nuevo tablero (NBoard), las direcciones restantes (Dirs), la lista de recorrido actualizada [(Npos, NuevoValor)|Recorrido], el nuevo valor (NuevoValor) y una variable de salida (V). @includedef{generar_recorridoAux/7}".
generar_recorridoAux(_, _, [], _, [], Valor, Valor).
generar_recorridoAux(Ipos, N, Board, DireccionesPermitidas, [(Npos, NuevoValor)|Recorrido], Valor, V):-
     select_dir(Dir, DireccionesPermitidas, Dirs),
     movimiento_valido(N, Ipos, Dir),
     efectuar_movimiento(Ipos, Dir, Npos),
     select_cell(Npos, Op, Board, NBoard),
     aplicar_op(Op, Valor, NuevoValor),
     generar_recorridoAux(Npos, N, NBoard, Dirs, Recorrido, NuevoValor, V).

:- pred generar_recorrido(PosN,N,Board,DireccionesPermitidas,Lista,V)
    #"El predicado selecciona la celda correspondiente a la posici@'{o}n inicial (Ipos) en el tablero (Board) utilizando el predicado select_cell. Luego, se aplica una operaci@'{o}n al valor 0 utilizando el predicado aplicar_op y se obtiene un nuevo valor (NuevoValor). A continuaci@'{o}n, se llama al predicado auxiliar generar_recorridoAux con los par@'{a}metros actualizados (Ipos, N, NBoard, DireccionesPermitidas, Recorrido, NuevoValor, V). Este predicado auxiliar se encarga de realizar la recursi@'{o}n para generar el recorrido completo en el tablero. El resultado final del recorrido se obtiene a trav@'{e}s de la variable de salida V. @includedef{generar_recorrido/6}".
generar_recorrido(Ipos,N,Board,DireccionesPermitidas,[(Ipos,NuevoValor)|Recorrido],V) :- 
     select_cell(Ipos,Op,Board,NBoard),
     aplicar_op(Op,0,NuevoValor),
     generar_recorridoAux(Ipos,N,NBoard,DireccionesPermitidas,Recorrido,NuevoValor,V).

:- pred generar_recorridos(N, Board, DireccionesPermitidas, Recorrido, Valor)
    #"Predicado que utiliza el member para seleccionar una de las celdas y una vez seleccionada, se generan los recorridos llamando al predicado generar_recorrido. @includedef{generar_recorridos/5}".
generar_recorridos(N, Board, DireccionesPermitidas, Recorrido, Valor) :-
    member(cell(Ipos,_),Board),
    generar_recorrido(Ipos,N,Board,DireccionesPermitidas,Recorrido,Valor). 


:- pred tablero(N, Tablero, DireccionesPermitidas, ValorMinimo, NumeroDeRutasConValorMinimo)
    #"Predicado que utiliza el predicado findall para generar una lista (Valores) de todos los valores obtenidos al llamar al predicado generar_recorridos y un valor no utilizado como salida. Verifica que la lista de valores (Valores) no est@'{e} vacia utilizando '\=' y llama al predicado minimo_repetido. @includedef{tablero/5}".
tablero(N, Tablero, DireccionesPermitidas, ValorMinimo, NumeroDeRutasConValorMinimo) :-
  findall(Valor,generar_recorridos(N, Tablero, DireccionesPermitidas, _, Valor),Valores),
  Valores \= [],
  minimo_repetido(Valores, ValorMinimo, NumeroDeRutasConValorMinimo).



:- pred minimo_repetido(Lista,Minimo,Repeticiones)
    #"Predicado que dada un lista, selecciona el valor minimo y cuantas veces se repite. Realiza una llamada recursiva al predicado minimo_repetido con el resto de la lista Xs, obteniendo el valor m@'{i}nimo Min y el n@'{u}mero de repeticiones hasta ese punto Repe. Se comparan los valores X y Min para determinar: si X < Min, se actualiza el minimo y las repeticiones, si X = Min, se aumentan las repeticiones y si X > Min se actualizan los datos Minimo y Repeticiones. @includedef{minimo_repetido/3}".
minimo_repetido([],_,0).
minimo_repetido([X|Xs], Minimo, Repeticiones) :-
    minimo_repetido(Xs, Min, Repe),
    (X @< Min -> (Minimo = X, Repeticiones = 1);
                (X = Min -> (Repeticiones is Repe + 1, Minimo = Min) ;
                            (Repeticiones = Repe, Minimo = Min))).


    



%%TESTS:
:- doc(hide, direcciones/1).
direcciones([n, s, e, o, ne, no, se, so]).
:- doc(hide, permit/1).
permit([dir(n,3), dir(s,4), dir(o,1), dir(e,10)]).

:- doc(hide, board1/1).
board1([cell(pos(1,1),op(*,-3)),
        cell(pos(1,2),op(-,1)),
        cell(pos(1,3),op(-,4)),
        cell(pos(1,4),op(- ,555)),
        cell(pos(2,1),op(-,3)),
        cell(pos(2,2),op(+ ,2000)),
        cell(pos(2,3),op(* ,133)),
        cell(pos(2,4),op(- ,444)),
        cell(pos(3,1),op(*,0)),
        cell(pos(3,2),op(* ,155)),
        cell(pos(3,3),op(//,2)),
        cell(pos(3,4),op(+ ,20)),
        cell(pos(4,1),op(-,2)),
        cell(pos(4,2),op(- ,1000)),
        cell(pos(4,3),op(-,9)),
        cell(pos(4,4),op(*,4))]).
:- doc(hide, board2/1).
board2([cell(pos(1,1),op(*,-3)),cell(pos(1,2),op(-,1)),cell(pos(2,1),op(-,3)),cell(pos(2,2),op(+,2000))]).
:- doc(hide, board3/1).
board3([cell(pos(1,1),op(+,1))]).







