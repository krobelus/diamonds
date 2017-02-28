module diamonds

import IO;
import lang::ofg::ast::Java2OFG;
import lang::ofg::ast::FlowLanguage;

public void main(list[str] args) {
	print_all();
	something();
}

set[str] containerClasses =  {
	 "/java/util/Map"
	,"/java/util/HashMap"
	,"/java/util/Collection"
	,"/java/util/Set"
	,"/java/util/HashSet"
	,"/java/util/LinkedHashSet"
	,"/java/util/List"
	,"/java/util/ArrayList"
	,"/java/util/LinkedList"
};

//public str path = "../eLib/Main.java";
public loc elib = |project://eLib/|;
public Program ofg;
public set[Decl] decls;
public set[Stm] stms;

public void set_up(loc location) {
	ofg = createOFG(location);
	decls = ofg[0];
	stms = ofg[1];
}

public void print_all() {
	set_up(elib);
	if(true) {
		visit(stms) {
			case n:newAssign(target, class, ctor, actualParameters): {
				println("new\t<target>");
				print("\t"); println(class);
				print("\t"); println(ctor);
				print("\t"); println(actualParameters);
				println("");
			}
			case a:assign(target, cast, source): {
				print("assign");
				print("\t"); println(target);
				print("\t"); println(cast);
				print("\t"); println(source);
				println("");
			}
			case c:call(target, cast, receiver, method, actualParameters): {
				print("call");
				print("\t"); println(target);
				print("\t"); println(cast);
				print("\t"); println(receiver);
				print("\t"); println(method);
				print("\t"); println(actualParameters);
				println("");
			}
		};
	}
	/*
	if(true) {
		visit(decls) {
			case a:attribute(id): {
				println("attribute\t<id>");
			}
			case m:method(id, formalParameters): {
				print("method\t");
				println(id);
				print("\t");
				println(formalParameters);
				println("");
			}
			case c:constructor(id, formalParameters): {
				print("constructor\t<id>\n\t");
				print(formalParameters);
				println("");
			}
		};
	}
	*/
}

public void something() {
	set_up(elib);
	loc loansloc = |java+field:///User/loans|;
	set[Decl] loansDecls = { a | /a:attribute(id) <- ofg, id == loansloc };
	//set[Stm] loansStms = { s | /s:newAssign(target, class, ctor, actualParameters) <- ofg, target == loansloc };
	loc tloc = |java+class:///java/util/LinkedList|;
	//set[Stm] newlists = { s | /s:newAssign(target, class, ctor, actualParameters) <- ofg, class == tloc };
	set[Stm] tmp = { s | /s:assign(target, cast, source) <- ofg, target == loansloc };
	tmp += { s | /s:call(target, cast, receiver, method, actualParameters) <- ofg };
	visit(tmp) {
		case s:assign(target, cast, source): {
			println(s);
		}
		case n:newAssign(target, class, ctor, actualParameters): {
			println("newAssign: <target>");
		}
		case c:call(target, cast, receiver, method, actualParameters): {
			if(method == |java+method:///User/addLoan(Loan)|)
				println("call\n\t<target>\n\t<cast>\n\t<receiver>\n\t<method>\n\t<actualParameters>\n");
		}
	}
}