module diamonds

import IO;
import lang::ofg::ast::Java2OFG;
import lang::ofg::ast::FlowLanguage;
import lang::java::jdt::m3::AST;

public set[str] containerClasses =  {
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

public set[str] containerClassesSimple = {basename | path <- containerClasses, /.*\/<basename:[^\/]*>$/ := path};

//public str path = "../eLib/Main.java";
public loc elib = |project://eLib/|;
public AST asts;
public Program ofg;
public set[Decl] decls;
public set[Stm] stms;

lrel[loc, str] suggestions = [];

public void main(list[str] args) {
	set_up(elib);
}

public void set_up(loc location) {
	ofg = createOFG(location);
	asts = createAstsFromEclipseProject(location, true);
	stms = {s | /Stm s:_ <- ofg};
	decls = {d | /Decl d:_ <- ofg};
}

public void print_all() {
	set_up(elib);
	visit(ofg) {
		case n:newAssign(target, class, ctor, actualParameters):
			println("Stm: newAssign\ntarget\t<target>\nclass\t<class>\nctor\t<ctor>\nparams\t<actualParameters>\n");
		case a:assign(target, cast, source):
			println("Stm: assign\ntarget\t<target>\ncast\t<cast>\nsource\t<source>\n");
		case c:call(target, cast, receiver, method, actualParameters):
			println("Stm: call\ntarget\t<target>\ncast\t<cast>\nreivr\t<receiver>\nmethod\t<method>\nparams\t<actualParameters>\n");
		case a:attribute(id):
				println("Dec: attribute\tid\t<id>");
		case m:method(id, formalParameters):
			println("Dec: method\nid\t<id>\nparams\t<formalParameters>\n");
		case c:constructor(id, formalParameters):
			println("Dec: ctor\nid\t<id>\nparams\t<formalParameters>\n");
	};
}

public loc infer_type(loc source) {
	println("inferring type of <source>");
	scheme = source.scheme;
	authority = source.authority;
	path = source.path;
	return switch(source.scheme) {
		case "java+parameter": {
			println("path is <path>");
			if(/<method:[^(]*>\(<tipo:[^)]*>\)/ := path) {
				//println("method is <method>, type is <tipo>");
				return |java+type:///<tipo>|;
			} else {
				return |error:///methodparse|;
			}
		}
		case _: {
			return |id:///|;
		}
	}
}

public void add_suggestion_for_loans() {
	set_up(elib);
	loc userloans = |java+field:///User/loans|;
	list[Stm] assignstouserloans = [ a | /a:assign(userloans, _, _) <- stms];
	println(assignstouserloans);
	Stm assignstm = assignstouserloans[0];
	assign(assigntarget, assigncast, assignsource) = assignstm;
	result = infer_type(assignsource);
	if(result.scheme == "java+type" && /.<tipo:.*>/ := result.path) {
		suggestions += <userloans, tipo>;
	} 
	println(suggestions);
}

public void something() {
	set_up(elib);
	lvalues = {id | attribute(id) <- decls} +
			{target | assign(target, cast, source) <- stms} +
			{target | newAssign(target, class, ctor, actualParameters) <- stms} +
			{target | call(target, cast, receive, method, actualParameters) <- stms}
			;
	llvalues = [l | l <- lvalues][1..3];
	collections = [<lname, varname, rname, L@src> | /f:field(simpleType(L:simpleName(lname:_)),
					//variable("loans", _, newObject(simpleType(R:simpleName(rname:_)))))
					[variable(varname:_, _, newObject(simpleType(R:simpleName(rname:_)), _))])
					<- asts, lname in containerClassesSimple]; 
	for(x <- collections) {
		println(x);
	}
}