package info.kwarc.sally.projects;
/*
import info.kwarc.mmt.api.Content;
import info.kwarc.mmt.api.DPath;
import info.kwarc.mmt.api.LocalName;
import info.kwarc.mmt.api.LocalPath;
import info.kwarc.mmt.api.MPath;
import info.kwarc.mmt.api.frontend.Controller;
import info.kwarc.mmt.api.frontend.NotFound;
import info.kwarc.mmt.api.libraries.Library;
import info.kwarc.mmt.api.modules.DeclaredTheory;
import info.kwarc.mmt.api.parser.TextNotation;
import info.kwarc.mmt.api.symbols.Constant;
import info.kwarc.mmt.api.symbols.DeclaredStructure;
import info.kwarc.mmt.api.symbols.PlainInclude;
import info.kwarc.mmt.api.symbols.TermContainer;
import info.kwarc.mmt.api.utils.URI;

import java.util.ArrayList;
import java.util.List;

import scala.Option;
import scala.collection.Iterator;

public class MMTWrapper {

	private static Option<MPath> noneMPath = Option.apply(null);
	private static Option<LocalName> noneLocalPath = Option.apply(null);
	private static Option<String> noneString = Option.apply(null);
	private static Option<TextNotation> noneTextNotation = Option.apply(null);

	static public DeclaredTheory createTheory(String file, String theoryName) {
		DPath docPath = new DPath(URI.apply(file));
		LocalPath localPath = new LocalPath(theoryName);
		return new DeclaredTheory(docPath, localPath, noneMPath);	
	}
	
	static public Constant createConstant(DeclaredTheory theory, String name) {
		return new Constant(theory.toTerm(), LocalName.apply(name), noneLocalPath, TermContainer.apply(""), TermContainer.apply(""), noneString, noneTextNotation);
	}
	
	static public ArrayList<String> getConstantsInTheory(Controller mmtController, DeclaredTheory theory) {
		ArrayList<String> result = new ArrayList<String>();
		scala.collection.immutable.List<Content> declList;
		Library lib = mmtController.memory().content();
		try {
			declList = lib.getDeclarationsInScope(theory.toTerm());
		} catch (Throwable e) {
			if (e instanceof NotFound) {
				NotFound nf = (NotFound) e;
				System.out.println("Could not find theory "+nf.path());
			}
			//e.printStackTrace();
			return result;
		}
		Iterator<Content> declIterator = declList.iterator();
		while (declIterator.hasNext()) {
			Content contentDecl = declIterator.next();
			if (contentDecl instanceof Constant) {
				Constant constantDecl = (Constant) contentDecl;
				result.add(constantDecl.name().toString());
			}
		}		
		return result;
	}
	
	static public List<DeclaredTheory> getAllTheories(Controller mmtController) {
		ArrayList<DeclaredTheory> result = new ArrayList<DeclaredTheory>();
		scala.collection.Iterable<MPath> theoryPaths = mmtController.memory().content().getAllPaths();
		Iterator<MPath> theoryIterator = theoryPaths.iterator();
		while (theoryIterator.hasNext()) {
			MPath path = theoryIterator.next();
			result.add((DeclaredTheory)mmtController.get(path));
		}
		return result;
	}
	
	static public DeclaredStructure createImport(DeclaredTheory from, DeclaredTheory to) {
		return PlainInclude.apply(to.path(), from.path());
	}
	
	public static void main(String[] args) {
		Controller mmtController = new Controller();
		DeclaredTheory adminCosts = createTheory("file:///home/costea/kwarc/stc/sissi/winograd/cds/admincosts.tex", "admincosts");
		DeclaredTheory accountingBase = createTheory("file:///some/path/accountingbase.tex", "accountingbase");

		mmtController.add(accountingBase);

		mmtController.add(createConstant(accountingBase, "money"));

		mmtController.add(adminCosts);
		
		mmtController.add(createImport(adminCosts, accountingBase));
		
		mmtController.add(createConstant(adminCosts, "admincostsperti"));
		
		getConstantsInTheory(mmtController, createTheory("file:///home/costea/kwarc/stc/sissi/winograd/cds/admincosts.tex", "admincosts"));
		
	}
	
}

*/
