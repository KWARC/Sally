package info.kwarc.references;

import org.junit.Test;

public class HTMLSectionProviderTest {

	String test = "<div class=\"field field-name-body field-type-text-with-summary field-label-above\"><div class=\"field-label\">Body:&nbsp;</div><div class=\"field-items\"><div class=\"field-item even\" property=\"content:encoded\"><div xmlns=\"http://www.w3.org/1999/xhtml\" class=\"document\">\n<div id=\"S1\" class=\"section\">\n<h2 class=\"title section-title\"><span class=\"tag\">1 </span>Doign comments</h2>\n<div id=\"S1.p1\" class=\"para\">\n<p id=\"S1.p1.1\" class=\"p\">In this section I want to show how commenting can work.</p>\n</div>\n<div id=\"S1.SS1\" class=\"subsection\">\n<h3 class=\"title subsection-title\"><span class=\"tag\">1.1 </span>Types of relations</h3>\n<div id=\"S1.SS1.p1\" class=\"para\">\n<p id=\"S1.SS1.p1.1\" class=\"p\">There are several types of relations.</p>\n</div>\n</div>\n</div>\n</div></div></div></div>";
	
	@Test
	public void test() {
		HTMLSectionProvider provider = new HTMLSectionProvider();
		provider.provide("xhtml", test, new IReferenceAcceptor() {

			public void accept(Object o) {
				System.out.println(o);
			}
		});
	}

}
