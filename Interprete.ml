type ide = string;;
type tval = TInt | TBool | TString;;
type exp = CstInt of int
        | CstTrue 
        | CstFalse
        | CstString of string
        | Den of ide
        | Sum of exp * exp
        | Prod of exp*exp
        | Sub of exp * exp
        | Times of exp * exp
        | Ifthenelse of exp * exp * exp
        | Eq of exp * exp
        | Greater of exp * exp
        | Let of ide * exp * exp
        | Fun of ide * exp
        | Letrec of ide * ide * exp * exp
        | Apply of exp * exp
        (*aggiunte all'interprete*)
        | EmptySet of tval (*costruttore che permette di creare un set vuoto*)
        | Singleton of tval*exp (*costruttore che permette di creare un set con un elemento se l'elemento ha lo stesso tipo del set*)
        | Insert of exp * exp (*costruttore che permette di inserire un elemento all'interno del set se l'elemento ha lo stesso tipo del set (ovviamente non aggiunge duplicati) *)
        | Remove of exp*exp (*costruttore che permette di rimuovere un elemento da un set*)
        | IsEmpty of exp (*costruttore che permette di verificare se un set è vuoto*)
        | IsInSet of exp*exp (*costruttore che permette di verificare se un elemento appartiene al set*)
        | Union of exp*exp (*costruttore che permette di fare unione di due set se e solo se hanno lo stesso tipo*)
        | Intersection of exp*exp (*costruttore che permette di fare l'intersezione di due set se e solo se hanno lo stesso tipo*)
        | Difference of exp*exp (*costruttore che permette di fare la differenza di due set se e solo se hanno lo stesso tipo*)
        | Subset of exp*exp (*costruttore che permette di verificare se un set è sottoinsieme di un altro set*)
        | MaxSet of exp (*costruttore che permette di trovare l'elemento massimo del set*)
        | MinSet of exp (*costruttore che permette di trovare l'elemento massimo del set*)
        | ForAll of exp*exp (*costruttore che restituisce true se il predicato passato come parametro è vero per ogni elemento del Set *)
        | Exsist of exp*exp (*costruttore che restituisce true se il predicato passato come parametro è vero per almeno un elemento del Set *)
        | Filter of exp*exp (*costruttore che restituisce il Set di elementi che appartengono al Set passato come parametro per i quali l'applicazione del predicato passato come parametro è uguale a true *)
        | Map of exp*exp ;; (*costruttore che applica una funzione ad ogni elemento del Set e restiruisce un Set contenente il risultato di tutte le applicazioni *)
        

type 'v env = (string * 'v) list;;

type evT = Int of int | Bool of bool | String of string |Set of tval * evT list | Closure of ide * exp * evT env | RecClosure of ide * ide * exp * evT env | Unbound;;

let emptyEnv  = [ ("", Unbound)] ;;

let bind (s: evT env) (i:string) (x:evT) = ( i, x ) :: s;;

let rec lookup (s:evT env) (i:string) = match s with
    | [] ->  Unbound
    | (j,v)::sl when j = i -> v
    | _::sl -> lookup sl i;;

let typecheck (x, y) = match x with    
        | "int" -> 
             (match y with 
                         | Int(u) -> true
                         | _ -> false)

        | "bool" -> 
              (match y with 
                          | Bool(u) -> true
                          | _ -> false)
    	| "string" ->
    	  		  (match y with 
                          | String(u) -> true
                          | _ -> false)
        | "set" ->
        		  (match y with 
                          | Set(_) -> true
                          | _ -> false)
        | _ -> failwith ("not valid type");;


let int_eq(x,y) =   
match (typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Bool(v = w)
  | (_,_,_,_) -> failwith("run-time error ");;
       
 let int_plus(x, y) = 
 match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v + w)
  | (_,_,_,_) -> failwith("run-time error ");;
  
 let int_prod(x, y) = 
 match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v * w)
  | (_,_,_,_) -> failwith("run-time error ");;
  
let int_sub(x, y) = 
 match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v - w)
  | (_,_,_,_) -> failwith("run-time error ");;

let int_times(x, y) = 
 match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v * w)
  | (_,_,_,_) -> failwith("run-time error ");;

let typeof (v:evT) : tval = match v with
    |Int(_)->TInt
    |String(_)->TString
    |Bool(_)->TBool
    |_->failwith("typeof is not defined for this type");;
    
let evtToexp (v:evT) : exp = match v with
    |Int(n)->CstInt(n)
    |String(s)->CstString(s)
    |Bool(b)->if (b=true) then CstTrue else CstFalse
    |_->failwith("evtToexp is not defined for this type");;
    
let remove (v:evT) (set:evT) =
    match(typecheck("set",set),set) with (*controllo se il secondo argomento è di tipo set*)
    |(true, Set(t,l))->if (typeof v = t) then (*se si controllo se il primo argomento ha lo stesso tipo del set*)
                (let rec aux l g = match l with
                |[] -> []
                |h::t -> if(h=g) then aux t g else h::aux t g  in Set(t,aux l v))
               else failwith("You cannot remove element that has different type than the set ")  (*Non necessario ma inserito per avvertire l'utente di un utilizzo errato della funzione *)
    | (_,_) -> failwith("run-time error ");;
    
let isin (v:evT) (set:evT) =
	match(typecheck("set",set),set) with (*controllo se il secondo argomento è di tipo set*)
    |(true, Set(t,l))->if (typeof v = t) then (*se si controllo se il primo argomento ha lo stesso tipo del set*)
                let rec aux l g = match l with
                |[] -> Bool(false)
                |h::t -> if(h=g) then Bool(true) else aux t g 
                in aux l v
               else Bool(false)  (*se l'elemento ha tipo diverso dal set posso dire direttamente che non è contenuto nel set*)
    | (_,_) -> failwith("run-time error: set and element of different types");;

let insert (v:evT) (set:evT) =
    match(typecheck("set",set),set) with (*controllo se il secondo argomento è di tipo set*)

    |(true, Set(t,l))->if (typeof v = t) then (*se si controllo se il primo argomento ha lo stesso tipo del set*)
    				(if(isin v set = Bool(true)) then Set(t,l) else Set(t,v::l)) (*inserisco elemento nella lista solo se non è già prersente nel set*)
               else failwith("You cannot insert element that has different type than the set")  
    | (_,_) -> failwith("run-time error ");;
    
let isempty (set:evT) = 
	match(typecheck("set",set),set) with (*controllo se l'argomento è di tipo set*)
    |(true, Set(t,l))->(match l with
    		|[]->Bool(true) (*Se la corrispettiva lista associata al set è vuota restituisci true *)
    		|_->Bool(false))
    | (_,_) -> failwith("run-time error: isEmpty is called on a non-Set evT");;
    
let union (set1:evT) (set2:evT) = 
	match(typecheck("set",set1),set1,typecheck("set",set2),set2) with (*controllo se il primo e il secondo argomento sono di tipo set*)
	|(true,Set(t1,l1),true,Set(t2,l2))-> if(t1=t2) then     (*controllo se i due set hanno lo stesso tipo*)  
													let rec aux l1 acc = match l1 with (*Utilizzo come accumulatore il set2 e inserisco tramite la procedura 
                                                                                        						    insert (che non inserisce duplicati) tutti gli elementi del primo set nell'accumulatore*)
													|[]->acc
													|h::t -> aux t (insert h acc)  
													in aux l1 set2
													else failwith("run-time error: you cannot merge two sets of different types")
	|(_,_,_,_)-> failwith("run-time error: Union is called on a non-Set evT");;
	
let intersection (set1:evT) (set2:evT) = 
	match(typecheck("set",set1),set1,typecheck("set",set2),set2) with (*controllo se il primo e il secondo argomento sono di tipo set*)
	|(true,Set(t1,l1),true,Set(t2,l2))-> if(t1=t2) then   (*controllo se i due set hanno lo stesso tipo*)   
													let rec aux l1 acc = match l1 with (*utilizzo come accumulatore un set vuoto*)
													|[]->acc (*Dopo che ho scandito tutto il primo set ritorno l'accumulatore che rappresenta il Set intersezione *)
													|h::t -> if((isin h set2) = Bool(true)) then aux t (insert h acc) else aux t acc (*Inserisco nell'accumulatore tutti gli elementi di set1 *)
													in aux l1 (Set(t1,[]))                                                            (*che sono presenti anche in set2 *)
													else failwith("run-time error: you cannot intersection two sets of different types")
	|(_,_,_,_)-> failwith("run-time error: Intersection is called on a non-Set evT");;
	
let difference (set1:evT) (set2:evT) = 
	match(typecheck("set",set1),set1,typecheck("set",set2),set2) with  (*controllo se il primo e il secondo argomento sono di tipo set*)
	|(true,Set(t1,l1),true,Set(t2,l2))-> if(t1=t2) then       (*controllo se i due set hanno lo stesso tipo*)
													let rec aux l1 acc = match l1 with (*utilizzo come accumulatore un set vuoto*)
													|[]->acc (*Dopo che ho scandito tutto il primo set ritorno l'accumulatore che rappresenta il Set differenza *)
													|h::t -> if((isin h set2) = Bool(false)) then aux t (insert h acc) else aux t acc (*Inserisco nell'accumulatore tutti gli elementi di set1 *)
													in aux l1 (Set(t1,[]))                                                            (*che NON sono presenti in set2 *)
													else failwith("run-time error: you cannot make a difference between two sets of different types")
	|(_,_,_,_)-> failwith("run-time error: Difference is called on a non-Set evT ");;
	
let subset (set1:evT) (set2:evT) =
	match(typecheck("set",set1),set1,typecheck("set",set2),set2) with (*controllo se il primo e il secondo argomento sono di tipo set*)
	|(true,Set(t1,l1),true,Set(t2,l2))-> if(t1=t2) then       (*controllo se i due set hanno lo stesso tipo*)
													let rec aux l1 = match l1 with
													|[]->Bool(true) (*Siamo arrivati in fondo alla lista => set1 ⊂ set2*)
													|h::t -> if((isin h set2) = Bool(true)) then aux t  else Bool(false) (*se tutti gli elementi di set1 sono contenuti in set2 => set1 ⊂ set2 *)
													in aux l1
										else Bool(false) (*se i set hanno tipo diverso posso dire drettamente che set1 non è sottoinsieme di set2 *)
	|(_,_,_,_)-> failwith("run-time error: Subset is called on a non-Set evT");;
	
let greater (v:evT) (t:evT)= match(v,t) with (*implementazione dell'operazione v è maggiore di t per i vari evT*)
	|(Int(n),Int(m))-> n>m
	|(Bool(true),Bool(_))->true
	|(Bool(false),Bool(_))->false
	|(String(n),String(m))->n>m
	|(_,_)->failwith("run-time error: you cannot compare element of different types");;
	
let max (set:evT) =
	match(typecheck("set",set),set) with (*controllo se l'argomento è di tipo set*)
    |(true, Set(t,l))->let smallest = match(t) with (*trovo il minimo valore per quel determinato tipo*)
    							|(TInt)->Int(min_int)
    							|(TBool)->Bool(false)
    							|(TString)->String("")			
    						  in 
    								let rec aux l m = match l with (*trovo il massimo valore nella lista*)
    								|[]->m
    								|h::t-> if ((greater h m)) then aux t h else aux t m in aux l smallest
    | (_,_) -> failwith("run-time error:the argument needs to be of Set type");;
let min (set:evT) =
	match(typecheck("set",set),set) with
    |(true, Set(t,l))->let first= match(l,t) with (*in questo caso conviene usare come massimo il primo elemento perchè non sappiamo quanto è il valore massimo di una stringa*)
    							|([],TInt)->Int(max_int) (*valore minimo set vuoto (come +∞)*)
    							|([],TBool)->Bool(true)  
    							|([],TString)->String("") (*se il set è vuoto la stringa di valore minimo è "" *)
    							|(h::t,_)->h (*uso primo elemento della lista se il set non è vuoto*)
    						  in 
    								let rec aux l m = match l with
    								|[]->m
    								|h::t-> if ((greater h m )) then aux t m else aux t h in aux l first
    | (_,_) -> failwith("run-time error:the argument needs to be of Set type ");;

let rev l= (*inverte una lista*)
	let rec aux l acc= match l with
	|[]-> acc
	|h::t-> aux t (h::acc) in aux l []


let rec eval  (e:exp) (s:evT env) = match e with
 | CstInt(n) -> Int(n)
 | CstTrue -> Bool(true)
 | CstFalse -> Bool(false)
 | CstString(s) -> String(s)
 | EmptySet(t) -> Set(t,[])
 | Singleton(t,e) -> let g= eval e s in 
 								if(typeof g == t) then Set(t,[g]) 
 								else failwith("the type of the argument doesn't match the type of the Set")
 | Insert(elem,set) ->  insert (eval elem s) (eval set s)
 | Remove(elem, set) -> remove (eval elem s) (eval set s)
 | IsEmpty(e) -> isempty (eval e s)
 | IsInSet(elem,set) -> isin (eval elem s) (eval set s)
 | Union (set1,set2)-> union (eval set1 s) (eval set2 s) (*set1 ∪ set2*)
 | Intersection (set1,set2)-> intersection (eval set1 s) (eval set2 s) (*set1 ∩ set2*)
 | Difference (set1,set2)-> difference (eval set1 s) (eval set2 s) (*set1\set2*)
 | Subset (set1,set2)-> subset (eval set1 s) (eval set2 s) (*set1 ⊂ set2 ?*)

 | ForAll(f,set) -> let eset = eval set s in 
 		(match eset with (*controllo se il secondo argomento è di tipo set*)
      	    | Set(typ,l)-> let rec aux lst = match lst with
         	                                    | []->Bool(true) (*siamo arrivati in fondo alla lista: l'applicazione del predicato restiruisce true per tutti gli elementi della lista *)
                                                | h::t-> let g = eval (Apply(f,evtToexp(h))) s in (*applica il predicato alla testa della lista: sarà l'apply stessa a verificare se il primo parametro è una funzione*)
            			                            (match (typecheck("bool", g)) with (*controllo se la funzione è un predicato, ovvero se restituisce un booleano*)
            				                            |true -> if(g=Bool(true)) then aux t else Bool(false)           (*Se è valido per la testa della lista chiamo ricorsivamente la funzione sulla coda; altrimenti ritorno false*)
            				                            |false -> failwith("the function doesn't return boolean type")) (*perchè esiste un elemento x tc f(x)=false: predicato non valido per tutti gli elementi della lista*)
                                                            in aux l 
            | _ -> failwith ("run-type error"))
  | Exsist(f,set) -> let eset = eval set s in 
        (match eset with (*controllo se il secondo argomento è di tipo set*)
            | Set(typ,l)-> let rec aux lst = match lst with
                                                | []->Bool(false) (*siamo arrivati in fondo alla lista: l'applicazione del predicato restiruisce false per tutti gli elementi della lista *)
                                                | h::t-> let g = eval (Apply(f,evtToexp(h))) s in (*applica il predicato alla testa della lista: sarà l'apply stessa a verificare se il primo parametro è una funzione*)
            			                            (match (typecheck("bool", g)) with (*controllo se la funzione è un predicato, ovvero se restituisce un booleano*)
            				                            |true -> if(g=Bool(true)) then Bool(true) else aux t            (*Se è valido per la testa della lista restituisco true altrimenti applico ricorsivamente la funzione sulla coda *)
            				                            |false -> failwith("the function doesn't return boolean type")) (*alla ricerca di un elemento x ∊ lista tc f(x)=true *)
                                                            in aux l 
            | _ -> failwith ("run-type error"))
 | Filter(f,set) -> let eset = eval set s in 
        (match eset with (*controllo se il secondo argomento è di tipo set*)
            | Set(typ,l)-> let rec aux lst = match lst with
                                                |[]->[]
                                                |h::t-> let g = eval (Apply(f,evtToexp(h))) s in (*applica il predicato alla testa della lista: sarà l'apply stessa a verificare se il primo parametro è una funzione*)
                                                    (match (typecheck("bool", g)) with (*controllo se la funzione è un predicato, ovvero se restituisce un booleano*)
            				                            |true -> if(g=Bool(true)) then h::aux t else aux t (*se il predicato è vero per la testa inserisco l'elemento nella lista che farà parte del mio Set*)
            				                            |false -> failwith("the function doesn't return boolean type"))
                                                            in Set(typ,aux l)
            | _ -> failwith ("run-type error"))
 | Map(f,set) -> let eset = eval set s in 
        (match eset with (*controllo se il secondo argomento è di tipo set*)
            | Set(typ,l)-> let rec aux lst acc ntyp= match lst with
                                                        |[]->Set(ntyp,rev acc)              (*ho applicato la funzione a tutti gli elementi della lista: restituisco il Set che contiene il risultato delle *)
                                                                                            (*applicazioni della funzione a tutti gli elementi del set e il tipo del nuovo set  *)

                                                        |h::t-> let g = eval (Apply(f,evtToexp(h))) s in (*applico la funzione alla testa della lista, conservo il risultato in un accumulatore e chiamo ricorsivamente la funzione sulla coda *)
                   			                                let typeElem = typeof g in (*calcolo il tipo del nuovo Set*)
                   				                                aux t (g::acc) typeElem 
                                                                    in aux l [] typ
            | _ -> failwith ("run-type error"))
 | MaxSet(set) -> max(eval set s)
 | MinSet(set) -> min(eval set s)
 | Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
 | Greater(e1,e2) -> Bool(greater (eval e1 s) (eval e2 s))
 | Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
 | Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
 | Prod(e1,e2) -> int_prod((eval e1 s), (eval e2 s))
 | Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
 | Ifthenelse(e1,e2,e3) -> let g = eval e1 s in
                (match (typecheck("bool", g), g) with
            | (true, Bool(true)) -> eval e2 s
                        | (true, Bool(false)) -> eval e3 s
                    | (_, _) -> failwith ("nonboolean guard"))
| Den(i) -> lookup s i
| Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
| Fun(arg, ebody) -> Closure(arg,ebody,s)
| Letrec(f, arg, fBody, letBody) -> 
  let benv = bind (s) (f) (RecClosure(f, arg, fBody,s)) in
      eval letBody benv
| Apply(eF, eArg) ->
    let fclosure = eval eF s in 
         (match fclosure with 
           | Closure(arg, fbody, fDecEnv) ->
             let aVal = eval eArg s in
          		let aenv = bind fDecEnv arg aVal in 
                eval fbody aenv
           | RecClosure(f, arg, fbody, fDecEnv) ->
             let aVal = eval eArg s in
               let rEnv = bind fDecEnv f fclosure in
              		let aenv = bind rEnv arg aVal in 
                    eval fbody aenv
           | _ -> failwith("non functional value"));; 

(*test effettuati*)
let e= EmptySet(TInt);;(*posso usare questa espressione ovunque è richiesto un tipo exp*)
eval e emptyEnv;;
eval (Singleton(TBool, CstTrue)) emptyEnv;; (*posso valutare direttamente l'espressione*)
(*prova inserimento elementi*)

let e= Insert(CstInt(3),e);;
eval e emptyEnv;; (*restituisce un set di tipo int contenente {3}*)
let e= Insert(CstInt(4),e);;
eval e emptyEnv;; (*restituisce un set di tipo int contenente {3,4}*)
let e= Insert(CstInt(4),e);;
eval e emptyEnv;; (*non inserisco duplicati*)
let w= Insert(CstString("ciao"),e);;
eval w emptyEnv;;(*non puoi inserire nel set elementi di tipo diverso dal set*)
let e= Insert(CstInt(7),e);;
let e= Insert(CstInt(8),e);;

(*prova rimozione elementi*)
let t=Remove(CstInt(3),e);;
eval e emptyEnv;;
eval t emptyEnv;;(*abbiamo rimosso elemento 3 dal set*)
eval (Remove(CstTrue,e)) emptyEnv;;(*eccezione non necessaria ma inserita per avvertire utente di un uso improprio dell'operazione*)

(*prova IsInSet e IsEmpty*)
eval (IsInSet(CstInt(3),t)) emptyEnv;;(*set senza il 3--->false*)
eval (IsInSet(CstInt(3),e)) emptyEnv;;(*set con il 3--->true*)
eval (IsEmpty(e)) emptyEnv;;
eval (IsEmpty(EmptySet(TInt))) emptyEnv;;

(*prova unione, itersezione e differenza*)
(*definisco due set: set1{4,5,6,2} ; set2{8,3,2,4}*)
let set1=Insert(CstInt(4),Insert(CstInt(5),Insert(CstInt(6),Singleton(TInt,CstInt(2)))));;
let set2=Insert(CstInt(8),Insert(CstInt(3),Insert(CstInt(2),Singleton(TInt,CstInt(4)))));;
eval (Union(set1,set2)) emptyEnv;;
eval (Intersection(set1,set2)) emptyEnv;;
eval (Difference(set1,set2)) emptyEnv;;

(*prova max,min,subset*)
eval (MaxSet(set1)) emptyEnv;;
eval (MinSet(set1)) emptyEnv;;
eval (MaxSet(EmptySet(TInt))) emptyEnv;;
eval (MinSet(EmptySet(TString))) emptyEnv;;
eval (Subset(set1,set2)) emptyEnv;;
let set3 = Insert(CstInt(5),Insert(CstInt(6),Singleton(TInt,CstInt(2))));; (*set3 ={5,6,2}*)
eval (Subset(set3,set1)) emptyEnv;;

(*prova ForAll, Exsist, Filter*)
let predicato = Fun("x",Ifthenelse(Greater(Den("x"),CstInt(3)),CstTrue,CstFalse));;
eval (ForAll(predicato,set3)) emptyEnv;;
eval (Exsist(predicato,set3)) emptyEnv;;
eval (Filter(predicato,set3)) emptyEnv;;
eval (ForAll(predicato,Filter(predicato,set3))) emptyEnv;; (*Filter ritorna un set:{5,6} che può essere usato nella ForAll*)
eval (ForAll(predicato,Filter(predicato,set3))) emptyEnv;;
let predicato= Fun("x", Ifthenelse(Eq(Letrec("fact", "n", Ifthenelse(Eq(Den("n"),CstInt(0)),CstInt(1),Prod(Den("n"),Apply(Den("fact"),Sub(Den("n"),CstInt(1))))), Apply(Den("fact"),Den("x"))),CstInt(120)),CstTrue,CstFalse));; (*se il fattoriale del numero è uguale a 120 ritorna true altrimenti false: 5! == 120*)
eval (ForAll(predicato,set3)) emptyEnv;;
eval (Exsist(predicato,set3)) emptyEnv;;
eval (Filter(predicato,set3)) emptyEnv;; (*ritorna il set contente tutti gli elementi il cui fattoriale è 120*)

(*prova ForAll, Exsist, Filter con funzione ricorsiva*)
let predicato= Fun("x", Ifthenelse(Greater(Letrec("fact", "n", Ifthenelse(Eq(Den("n"),CstInt(0)),CstInt(1),Prod(Den("n"),Apply(Den("fact"),Sub(Den("n"),CstInt(1))))), Apply(Den("fact"),Den("x"))),CstInt(119)),CstTrue,CstFalse));; (*se il fattoriale del numero è maggiore di 119 ritorna true altrimenti false: 5! == 120*)
eval (ForAll(predicato,set1)) emptyEnv;;
eval (Exsist(predicato,set1)) emptyEnv;;
eval (Filter(predicato,set1)) emptyEnv;; (*ritorna il set contente tutti gli elementi il cui fattoriale è maggiore di 119*)

(*prova Map*)
let funzione = Fun("x",Sum(Den("x"),CstInt(3)));;
eval (Map(funzione,set2)) emptyEnv;; (*somma 3 a tutti gli elementi del set2*)
let funzione = Fun("x",Ifthenelse(Greater(Den("x"),CstInt(3)),CstString("ok"),CstString("non ok")));;(*se il numero è maggiore di 3 ritorna la stringa ok altrimenti non ok*)
eval (Map(funzione,set2)) emptyEnv;; (*applica funzione a tutti gli elementi del set; cambia anche il tipo di ritorno*)

(*prova Map con funzione ricorsiva*)
let funzione = Fun("x", (Letrec("fact", "n", Ifthenelse(Eq(Den("n"),CstInt(0)),CstInt(1),Prod(Den("n"),Apply(Den("fact"),Sub(Den("n"),CstInt(1))))), Apply(Den("fact"),Den("x")))));; (*applica il fattoriale all'argomento passato comeparametro*)
eval (Map(funzione,set1)) emptyEnv;; (*ritorna un set che applica il fattoriale ad ogni elemento: set1={4,5,6,2}---->{24,120,720,2}*)
eval set2 emptyEnv;;
eval (Map(funzione,set2)) emptyEnv;;
