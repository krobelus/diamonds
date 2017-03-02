module diamonds

import IO;
import List;
import lang::ofg::ast::Java2OFG;
import lang::ofg::ast::FlowLanguage;
import lang::java::jdt::m3::AST;

public bool verbose = false;
public loc elib = |project://eLib/|;
public loc project;
public AST asts;
public Program ofg;
public set[Decl] decls;
public set[Stm] stms;
public map[loc, loc] declToType;

lrel[loc, str] suggestions = [];

rel[loc, str] expectedSuggestions = {
	<|java+field:///User/loans|, "Collection\<Loan\>">
	/*
	,<|java+field:///Library/loans|, "Collection\<Loan\> loans = new LinkedList\<\>();">
	,<|java+field:///Library/documents|, "Map\<Integer, Document\> = new HashMap\<\>();">
	,<|java+field:///Library/users|, "Map\<Integer, User\> = new HashMap\<\>();">
	,<|java+method:///Library/searchUser(String)/return|, "public List\<User\> searchUser(String name)">
	,<|java+variable:///Main/searchUser(String)/users|, "List\<User\> users = lib.searchUser(args[0]);">
	,<|java+variable:///Main/searchDoc(String)/docs|, "List\<Document\> docs = lib.searchDocumentByTitle(args[0]);">
	,<|java+variable:///Library/searchUser(String)/usersFound|, "List\<User\> usersFound = new LinkedList\<\>();">
	,<|java+method:///Library/searchDocumentByTitle(String)/return|, "public List\<Document\> searchDocumentByTitle(String)">
	,<|java+variable:///Library/searchDocumentByTitle(String)/docsFound|, "List\<Document\> docsFound = new LinkedList\<\>();">
	,<|java+method:///Library/searchDocumentByAuthor(String)/return|, "public List\<Document\> searchDocumentByAuthor(String)">
	*/
	,<|java+variable:///Library/searchDocumentByAuthor(String)/docsFound|, "List\<Document\>">
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

public set[str] mapClasses = {
	"/java/util/Map"
   ,"/java/util/HashMap"
};

public str basename(str path) {
	if(/\/<basename:[^\/]*>$/ := path)
		return basename;
	return "";
}
public str dirname(str path) {
	if(/<dirname:.*\/>/ := path)
		return dirname;
	return "";
}
public str pbasename(str path) {
	if(/<basename:[^\.]*$>/ := path)
		return basename;
	return "";
}
public set[str] containerClassesSimple = {basename(path) | path <- containerClasses};

public void main(list[str] args) {
	if(isEmpty(args))
		project = elib;
	else
		project = |project://<args[0]>|;
		/*
		{
			file = args[0];
			if(file[0] == "/")
				project = |file://<file>|;
			else
				project = |cwd:///<file>|;
		}
		*/
	add_suggestions();
	for(<var, newtype> <- suggestions) println("suggestion: declare <var>
											   '                 as <newtype>");
}

public void set_up(loc location) {
	ofg = createOFG(location);
	asts = createAstsFromEclipseProject(location, true);
	stms = {s | /Stm s:_ <- ofg};
	decls = {d | /Decl d:_ <- ofg};

	// FIXME only single fragments are supported atm for fields / vars
	// e.g. "List x;" but not "List x, j;" 
	fieldToType = (frag@decl: tipo@decl | /field(simpleType(tipo:_), frags:[frag:_]) <- asts);
	varToType = (frag@decl: tipo@decl | /variables(simpleType(tipo:_), frags:[frag:_]) <- asts);
	methToType = (m@decl: tipo@decl | /m:method(simpleType(tipo:_), name:_, parameters:_, exceptions:_, impl:_) <- asts)
			   + (m@decl: tipo@decl | /m:method(simpleType(tipo:_), name:_, parameters:_, exceptions:_) <- asts);
	declToType = fieldToType + varToType + methToType;
}

public void print_all() {
	set_up(project);
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

public str infer_type(loc target) {
	if(verbose) println("inferring type of <target>");
	list[loc] sources = [];
	// FIXME implement casts
	switch(target.scheme) {
		// hmm
		case "java+parameter": {
			if(/<method:[^(]*>\(<tipo:[^)]*>\)/ := target.path)
				return "<tipo>";
		}
		case "java+constructor": {
			if(/<tipo:[^(]*>/ := basename(target.path))
				return tipo; 
		}
		case "java+variable":
			;
		case "java+field":
			;
		case "java+method": {
			retval = target + "/return";
			sources = [ source | assign(retval, _, source:_) <- stms];
		}
	};
	tipo = declToType[target];
	if(!isContainer(tipo))
		return basename(tipo.path);
	if(isEmpty(sources)) {
		sources = [ source | assign(target, _, source:_) <- stms]
				+ [ source | call(target, _, _, source:_, _) <- stms]
				;
	}
	for(source <- sources) {
		return infer_type(source);
	}
	return "error: unknown";
}

public str infer_key_type(loc var) {
	// var is the location of the Map instance
	// just search for any .put assignment and derive the type of the key
	puts = [ key | /m:methodCall(_, recv:_, "put", [key:_, _]) <- asts, recv@decl == var];
	if(isEmpty(puts))
		return "ERROR";
	else
		return infer_type(puts[0]@decl);
}

/* TODO does this catch exactly what we want? (only parameterless generic containers)
 * qualifiedType is missing for sure, as well as wildcard (?)  
 **/
public bool isContainer(loc tipo) {
	return (tipo.scheme == "java+interface" || tipo.scheme == "java+class")
		&& tipo.path in containerClasses;
}

public void add_suggestions() {
	set_up(project);
	for(var <- declToType) {
		tipo = declToType[var];
		//if(var != |java+variable:///Main/searchDoc(java.lang.String)/docs|)
		//	continue;
		if(!isContainer(tipo))
			continue;
		// println("\nvar: <var>, type: <tipo>");
		types = [];
		if(tipo.path in mapClasses)
			types += infer_key_type(var);
		types += infer_type(var);
		generic = basename(tipo.path);
		correction = "<generic>\<<intercalate(", ", types)>\>";
		suggestions += <var, correction>;
	}
}