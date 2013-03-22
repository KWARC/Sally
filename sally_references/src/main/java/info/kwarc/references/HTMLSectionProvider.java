package info.kwarc.references;

import org.htmlcleaner.HtmlCleaner;
import org.htmlcleaner.HtmlNode;
import org.htmlcleaner.TagNode;
import org.htmlcleaner.TagNodeVisitor;

import sally.XMLNotification;
import sally.XMLPosition;

public class HTMLSectionProvider implements ReferenceProvider {
	HtmlCleaner cleaner;

	public HTMLSectionProvider() {
		cleaner = new HtmlCleaner();
	}

	public void provide(String format, String contents, final IReferenceAcceptor acceptor) {
		TagNode dom = cleaner.clean(contents);
		dom.traverse(new TagNodeVisitor() {
			public boolean visit(TagNode parentNode, HtmlNode htmlNode) {
				if (!(htmlNode instanceof TagNode))
					return true;
				TagNode node = (TagNode) htmlNode;
				if (!node.hasAttribute("class"))
					return true;
				if (node.getAttributeByName("class").contains("section-title")) {
					String text = node.getText().toString().toLowerCase();
					text = text.replaceAll("[0-9\\. ]*", "");
					acceptor.accept(XMLNotification.newBuilder()
							.setPos(XMLPosition.newBuilder().setXpath(String.format("//%s[@class='%s']",node.getName(), node.getAttributeByName("class")))).setUri(String.format("section/%s",text))
							.setMsg(String.format("Section %s", node.getText()))
							.build());
					return true;
				}
				return true;
			}
		});
	}
}