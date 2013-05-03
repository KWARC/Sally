package info.kwarc.references;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import sally.TextNotification;
import sally.TextPosition;

public class LaTeXSectionProvider implements ReferenceProvider {

	public void provide(String format, String contents,
			IReferenceAcceptor acceptor) {
		Pattern sectionPattern = Pattern.compile("\\\\(sub)*section\\{([a-zA-Z0-9 ]+)\\}");
		int lineCo = 0;
		for (String line : contents.split("\n")) {
			Matcher m = sectionPattern.matcher(line);
			int lastPos = 0;
			while (lastPos < line.length() && m.find(lastPos)) {
				lastPos = m.end() + 1;
				String text = m.group(2).toLowerCase();
				text = text.replaceAll("[0-9\\. ]*", "");
				TextPosition pos = TextPosition.newBuilder().setLine(lineCo).setCol(m.start()).build();
				
					
				acceptor.accept(TextNotification.newBuilder()
						.setPos(pos)
						.setUri(String.format("section/%s",text))
						.setMsg((String.format("Section %s", m.group(2))))
						.build());
			}			
			lineCo++;
		}
	}
	
}
