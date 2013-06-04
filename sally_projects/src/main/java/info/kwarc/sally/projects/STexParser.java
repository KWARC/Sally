package info.kwarc.sally.projects;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyService;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.io.IOUtils;
import org.apache.commons.vfs2.FileObject;
import org.apache.commons.vfs2.FileSelector;
import org.apache.commons.vfs2.FileSystemException;

public class STexParser {

	Pattern comments = Pattern.compile("%(.)*\n");
	Pattern sms = Pattern.compile("\\\\((begin|end)\\{(module|symboldec)\\}|importmodule)");
	Pattern idParser = Pattern.compile("^\\[[^\\]]*id=([a-zA-Z0-9-_]+)[^\\]]*\\]");
	Pattern symbolModule = Pattern.compile("^\\[[^\\]]*name=([a-zA-Z0-9-_]+)[^\\]]*\\]");
	Pattern importModule = Pattern.compile("^\\[([^\\]]*)\\]\\{([a-zA-Z0-9-_]+)\\}");
	Pattern extensionRemover = Pattern.compile("\\.[a-zA-Z0-9]+$");
	Pattern pathMacro = Pattern.compile("^\\\\([a-zA-Z0-9-_]+)\\{(.*)\\}$");

	public STexParser() {
	}
	
	public String getContent(InputStream is) {
		StringWriter writer = new StringWriter();
		try {
			IOUtils.copy(is, writer, "UTF-8");
		} catch (IOException e) {
			e.printStackTrace();
		}
		return writer.toString();
	}

	public String resolvePath(String file, SallyInteraction interaction) {
		Matcher m = pathMacro.matcher(file);
		if (m.find()) {
			String prefix = m.group(1);
			String path = m.group(2);
			String resPath = interaction.getOneInteraction("/alias/resolve", prefix, String.class);
			if (resPath != null)
				return resPath+"/"+path;
			else
				return "file:///unknown/alias/"+prefix+"/"+path;
		}
		return file;
	}

	public void sTeXToMMT(String stex, String fileURL, SallyInteraction interaction, STeXParsingEvents handler) {
		// remove comments
		stex = stex.replaceAll(comments.pattern(), "");
		Matcher smsMatcher = sms.matcher(stex);

		for (int start = 0; smsMatcher.find(start);) {
			// begin or end module
			start = smsMatcher.end();

			if ("begin".equals(smsMatcher.group(2)) && "module".equals(smsMatcher.group(3))) {
				Matcher idMatcher = idParser.matcher(stex.subSequence(start, stex.length()));
				if (idMatcher.find()) {
					start += idMatcher.end();
					handler.beginModule(fileURL, idMatcher.group(1), start);
				} else {
					System.out.println("Module without id in "+fileURL);
				}
			} else			
				if ("begin".equals(smsMatcher.group(2)) && "symboldec".equals(smsMatcher.group(3))) {
					Matcher symbolMatcher = symbolModule.matcher(stex.subSequence(start, stex.length()));				
					if (symbolMatcher.find()) {
						start += symbolMatcher.end();
						handler.symbolDec(symbolMatcher.group(1), start);
					} else {
						System.out.println("Symbol without declarations");
					}				
				} else			
					if ("importmodule".equals(smsMatcher.group(1))) {
						Matcher importMatcher = importModule.matcher(stex.subSequence(start, stex.length()));
						if (importMatcher.find()) {
							String uri = resolvePath(importMatcher.group(1), interaction);
							String theoryName = importMatcher.group(2);
							start += importMatcher.end();
							handler.importModule(uri, theoryName, start);
						} else {
							System.out.println("import module parameters could not be parsed");
						}
					}
		}
	}

	public String removeExtension(String fileName) {
		return extensionRemover.matcher(fileName).replaceFirst("");
	}

	public void doIndex(SallyInteraction interaction, FileSelector selector, FileObject root) {
		try {
			for (FileObject file : root.findFiles(selector)) {
				String stex = getContent(file.getContent().getInputStream());
				String fileURI = removeExtension(file.getURL().toString());

				sTeXToMMT(stex, fileURI, interaction, new MMTIndexHandler(interaction));
			}
		} catch (FileSystemException e) {
			e.printStackTrace();
		}
	}

	@SallyService(channel="/indexes")
	public void indexingService(String op, SallyActionAcceptor acceptor, SallyContext context) {
		acceptor.acceptResult("stex");
	}
	
}
