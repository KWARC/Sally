package info.kwarc.sally.projects;

import info.kwarc.mmt.api.frontend.Controller;
import info.kwarc.mmt.api.modules.DeclaredTheory;
import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyService;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.io.IOUtils;
import org.apache.commons.vfs2.FileObject;
import org.apache.commons.vfs2.FileSelector;
import org.apache.commons.vfs2.FileSystemException;

public class MMTService {

	Pattern comments = Pattern.compile("%(.)*\n");
	Pattern sms = Pattern.compile("\\\\((begin|end)\\{(module|symboldec)\\}|importmodule)");
	Pattern idParser = Pattern.compile("^\\[[^\\]]*id=([a-zA-Z0-9-_]+)[^\\]]*\\]");
	Pattern symbolModule = Pattern.compile("^\\[[^\\]]*name=([a-zA-Z0-9-_]+)[^\\]]*\\]");
	Pattern importModule = Pattern.compile("^\\[([^\\]]*)\\]\\{([a-zA-Z0-9-_]+)\\}");
	Controller mmtController;

	public MMTService() {
		mmtController = new Controller();
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

	public String resolvePath(String file, String rootURL) {
		file = file.replaceAll("\\\\SiSsI\\{", rootURL+"/");
		file = file.replaceAll("\\\\KWARCslides\\{", rootURL+"/../slides/");
		file = file.replaceAll("\\}", "");
		System.out.println("resolved "+file);
		return file;
	}
	
	public void sTeXToMMT(String stex, String fileURL, String rootURL) {
		// remove comments
		System.out.println(fileURL);
		stex = stex.replaceAll(comments.pattern(), "");
		Matcher smsMatcher = sms.matcher(stex);

		DeclaredTheory current = null;

		for (int start = 0; smsMatcher.find(start);) {
			// begin or end module
			start = smsMatcher.end();

			if ("begin".equals(smsMatcher.group(2)) && "module".equals(smsMatcher.group(3))) {
				Matcher idMatcher = idParser.matcher(stex.subSequence(start, stex.length()));
				if (idMatcher.find()) {
					current = MMTWrapper.createTheory(fileURL, idMatcher.group(1));
					mmtController.add(current);					
					start += idMatcher.end();
				} else {
					System.out.println("Module without id in "+fileURL);
				}
			} else			
				if ("begin".equals(smsMatcher.group(2)) && "symboldec".equals(smsMatcher.group(3))) {
					Matcher symbolMatcher = symbolModule.matcher(stex.subSequence(start, stex.length()));				
					if (symbolMatcher.find()) {
						if (current == null) 
							continue;
						mmtController.add(MMTWrapper.createConstant(current, symbolMatcher.group(1)));
						start += symbolMatcher.end();
					} else {
						System.out.println("Symbol without declarations");
					}				
				} else			
					if ("importmodule".equals(smsMatcher.group(1))) {
						Matcher importMatcher = importModule.matcher(stex.subSequence(start, stex.length()));
						if (importMatcher.find()) {
							if (current == null) 
								continue;
							String uri = resolvePath(importMatcher.group(1), rootURL);
							String theoryName = importMatcher.group(2);
							mmtController.add(MMTWrapper.createImport(current, MMTWrapper.createTheory(uri, theoryName)));
						} else {
							System.out.println("import module parameters could not be parsed");
						}
					}
		}
	}

	public void doIndex(SallyInteraction interaction, FileSelector selector) {
		List<FileObject> lst = interaction.getPossibleInteractions("/project", "get", FileObject.class);
		try {
			for (FileObject root : lst) {
				for (FileObject file : root.findFiles(selector)) {
					String stex = getContent(file.getContent().getInputStream());
					sTeXToMMT(stex, file.getName().getParent().getPath() +"/" + file.getName().getBaseName(), root.getURL().toString());
				}
			}
		} catch (FileSystemException e) {
			e.printStackTrace();
		}
	}

	@SallyService(channel="/queryMMT")
	public void doQuery(String query, SallyActionAcceptor acceptor, SallyContext context) {

	}
}
