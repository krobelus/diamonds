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
	add_suggestions();
	for(<var, newtype> <- suggestions) println("suggestion: declare <var>
											   '                 as <newtype>");
}

public void set_up(loc location) {
	suggestions = [];
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

public list[str] super_types(str tipo) {
	extends = [s@decl | /\class(tipo, [simpleType(s:simpleName(_))], _, _) <- asts];
	if(!isEmpty(extends)) {
		return [tipo] + super_types(extends[0].path[1..]); 
	}
	return [tipo, "Object"];
}

public str least_common_super_type(list[str] types) {
	if(size(types) == 1)
		return types[0];
	stypes = [super_types(tipo) | tipo <- types];
	if(isEmpty(stypes))
		return "error: super types";
	bool common; 
	for(t <- stypes[0]) {
		common = true;
		for(other <- stypes[1..]) {
			if(indexOf(other, t) == -1)
				common = false;
		}
		if(common)
			return t;
	}
}

public loc cast_or_source(loc cast, loc source) {
	if(cast != |id:///|)
		return cast;
	return source;
}

public str infer_type(loc target) {
	if(verbose) println("inferring type of <target>");
	list[loc] sources = [];
	// FIXME implement casts
	switch(target.scheme) {
		case "java+parameter":
			if(/<method:[^(]*>\(<tipo:[^)]*>\)/ := target.path)
				return "<tipo>";
		case "java+constructor":
			if(/<tipo:[^(]*>/ := basename(target.path))
				return tipo; 
		case "java+class":
			return target.path;
		case "java+variable":
			;
		case "java+field":
			;
		case "java+method": {
			retval = target + "/return";
			sources = [ cast_or_source(cast, source) | assign(retval, cast:_, source:_) <- stms];
		}
	};
	tipo = declToType[target];
	if(!isContainer(tipo))
		return basename(tipo.path);
	if(isEmpty(sources)) {
		casts = [ cast | assign(target, cast:_, source:_) <- stms];
		sources = [ cast_or_source(cast, source) | assign(target, cast:_, source:_) <- stms]
				+ [ cast_or_source(cast, source) | call(target, _, cast:_, source:_, _) <- stms];
	}
	types = [ infer_type(source) | source <- sources];
	if(!isEmpty(types)) {
		return least_common_super_type(types);
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