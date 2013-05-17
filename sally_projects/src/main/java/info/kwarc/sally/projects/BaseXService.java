package info.kwarc.sally.projects;
import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyService;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.net.URL;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.commons.io.IOUtils;
import org.apache.commons.vfs2.FileObject;
import org.apache.commons.vfs2.FileSelector;
import org.apache.commons.vfs2.FileSystemException;
import org.basex.core.cmd.CreateDB;
import org.basex.core.cmd.Open;
import org.basex.core.cmd.XQuery;
import org.basex.server.ClientSession;


public class BaseXService {
	ClientSession session;

	public BaseXService(String host, int Port, String User, String password) {
		try {
			session = new ClientSession("localhost", 1984, "admin", "admin");
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private String getDBNameFromURL(URL url) {
		String s = url.toString();
		s = s.replaceAll("[/|:]", "_");
		return s;
	}

	private void openOrCreateDatabase(String dbName) {
		String result = null;
		try {
			result = session.execute(new Open(dbName));
		} catch (IOException e1) {
		}
		if (result != null) {
			return;
		}
		try {
			session.execute(new CreateDB(dbName));
		} catch (IOException e) {
		}
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
	
	public Set<String> getDBFileList(String dbName) {
		Set<String> result = new HashSet<String>();

		String query = String.format("for $doc in collection('%s') return base-uri($doc)", dbName);
		try {
			String res = session.execute(new XQuery(query));
			System.out.println(res);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return result;
	}
	
	public void doIndex(SallyInteraction interaction, FileSelector selector) {
		List<FileObject> lst = interaction.getPossibleInteractions("/project", "get", FileObject.class);
		for (FileObject root : lst) {
			try {
				String dbName = getDBNameFromURL(root.getURL());
				openOrCreateDatabase(dbName);
				Set<String> existingFiles = getDBFileList(dbName);
				/*
				String rootPath = root.toString();
				for (FileObject file : root.findFiles(selector)) {
					String fileName = file.toString().substring(rootPath.length());
					Replace addOp = new Replace(fileName, getContent(file.getContent().getInputStream()));
					
					try {
						session.execute(addOp);
					} catch (IOException e1) {
						e1.printStackTrace();
					}
				}
				*/
			} catch (FileSystemException e2) {
				// TODO Auto-generated catch block
				e2.printStackTrace();
			}
		}
	}

	@SallyService(channel="/queryXML")
	public void doQuery(String query, SallyActionAcceptor acceptor, SallyContext context) {
	}

}
