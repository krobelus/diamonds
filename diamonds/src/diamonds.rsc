module diamonds

import IO;
import List;
import lang::ofg::ast::Java2OFG;
import lang::ofg::ast::FlowLanguage;
import lang::java::jdt::m3::AST;

public loc elib = |project://eLib/|;
public AST asts;
public Program ofg;
public set[Decl] decls;
public set[Stm] stms;
public map[loc, loc] declToType;

lrel[loc, str] suggestions = [];

rel[loc, str] expectedSuggestions = {
	<|java+field:///User/loans|, "Collection\<Loan\>">,
	/*
	<|java+field:///Library/loans|, "Collection\<Loan\> loans = new LinkedList\<\>();">,
	<|java+field:///Library/documents|, "Map\<Integer, Document\> = new HashMap\<\>();">,
	<|java+field:///Library/users|, "Map\<Integer, User\> = new HashMap\<\>();">,
	<|java+method:///Library/searchUser(String)/return|, "public List\<User\> searchUser(String name)">,
	<|java+variable:///Main/searchUser(String)/users|, "List\<User\> users = lib.searchUser(args[0]);">,
	<|java+variable:///Main/searchDoc(String)/docs|, "List\<Document\> docs = lib.searchDocumentByTitle(args[0]);">,
	<|java+variable:///Library/searchUser(String)/usersFound|, "List\<User\> usersFound = new LinkedList\<\>();">,
	<|java+method:///Library/searchDocumentByTitle(String)/return|, "public List\<Document\> searchDocumentByTitle(String)">,
	<|java+variable:///Library/searchDocumentByTitle(String)/docsFound|, "List\<Document\> docsFound = new LinkedList\<\>();">,
	<|java+method:///Library/searchDocumentByAuthor(String)/return|, "public List\<Document\> searchDocumentByAuthor(String)">,
	*/
	<|java+variable:///Library/searchDocumentByAuthor(String)/docsFound|, "List\<Document\>">
};

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

public str basename(str path) {
	if(/.*\/<basename:[^\/]*>$/ := path)
		return basename;
	return "";
}
public set[str] containerClassesSimple = {basename(path) | path <- containerClasses};

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
			println("Stm: newAssign\ntarget\t<target
			>\nclass\t<class>\nctor\t<ctor>\nparams\t<actualParameters>\n");
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

public list[loc] infer_type(loc source) {
	println("inferring type of <source>");
	scheme = source.scheme;
	authority = source.authority;
	path = source.path;
	return switch(source.scheme) {
		case "java+parameter": {
			// println("path is <path>");
			if(/<method:[^(]*>\(<tipo:[^)]*>\)/ := path) {
				//println("method is <method>, type is <tipo>");
				return [|java+type:///<tipo>|];
			} else {
				return [|error:///methodparse|];
			}
		}
		case _: {
			return [|id:///|];
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

/* TODO does this catch exactly what we want? (only parameterless generic containers)
 * qualifiedType is missing for sure, as well as wildcard (?)  
 **/
public bool isContainer(loc tipo) {
	return (tipo.scheme == "java+interface" || tipo.scheme == "java+class")
		&& tipo.path in containerClasses;
}

public void add_suggestions() {
	set_up(elib);
	
	// FIXME only single fragments are supported atm for fields / vars
	// e.g. "List x;" but not "List x, j;" 
	fieldToType = (frag@decl: tipo@decl | /field(simpleType(tipo:_), frags:[frag:_]) <- asts, isContainer(tipo@decl));
	varToType = (frag@decl: tipo@decl | /variables(simpleType(tipo:_), frags:[frag:_]) <- asts, isContainer(tipo@decl));
	methToType = (m@decl: tipo@decl | /m:method(simpleType(tipo:_), name:_, parameters:_, exceptions:_, impl:_) <- asts, isContainer(tipo@decl))
			   + (m@decl: tipo@decl | /m:method(simpleType(tipo:_), name:_, parameters:_, exceptions:_) <- asts, isContainer(tipo@decl));
	declToType = fieldToType + varToType + methToType;
	// for(m <- methToType) { println("methtotype: <m>: <methToType[m]>"); }
	//news = [n | n:newAssign(target, class, ctor, actualParameters) <- stms];
	//loc userloans = |java+field:///User/loans|;
	//println("\nNEW"); for(n:newAssign(userloans, class, ctor, actualParameters) <- stms) println(class);
	//println("\nASSIGN"); for(a:assign(userloans, cast, source) <- stms) println(source);
	//for(m <- declToType) println("declToType: <m>: <declToType[m]>");
	
	for(var <- declToType) {
		tipo = declToType[var];
		// if(tipo != |java+interface:///java/util/Map|) continue;
		println("\nvar: <var>, type: <tipo>");
		assigns = [ a | a:assign(var, _, _) <- stms];
		for(assign(_, cast, source) <- assigns) print("assign: cast <cast>, source <source>\n\n");
		bool found = false;
		for(assign(target, cast, source) <- assigns) {
			types = infer_type(source);
			types = [tipo | result <- types, result.scheme == "java+type", /.<tipo:.*>/ := result.path];
			if(!isEmpty(types)) {
				generic = basename(declToType[var].path);
				correction = "<generic>\<<intercalate(", ", types)>\>";
				suggestions += <var, correction>;
				found = true;
				// break;
			}
		}
		if(!found) {
			println("could not infer type for <var>");
		}
		// break;
	}
	for(<var, newtype> <- suggestions) println("suggestion: declare <var>\n\tas <newtype>");
}