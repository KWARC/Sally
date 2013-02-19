package info.kwarc.references;

import org.junit.Test;

public class LaTeXSectionProviderTest {

	String test1 = "\\section{Doign comments}\n\nIn this section I want to show how commenting can work.\n\n\\subsection{Types of relations}\n\nThere are several types of relations.";
	
	@Test
	public void test() {
		LaTeXSectionProvider provider = new LaTeXSectionProvider();
		provider.provide("tex", test1, new IReferenceAcceptor() {
			public void accept(Object o) {
				System.out.println(o);
			}
		});
	}
}
