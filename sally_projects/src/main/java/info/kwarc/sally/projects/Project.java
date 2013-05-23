package info.kwarc.sally.projects;
import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.networking.cometd.ConfigMeta;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.io.IOUtils;
import org.apache.commons.vfs2.FileObject;
import org.apache.commons.vfs2.FileSystemException;
import org.apache.commons.vfs2.VFS;

public class Project {

	FileObject root;
	String path;

	List<IndexHandler> indexers;
	
	public Project(String localPath) {
		indexers = new ArrayList<IndexHandler>();
		try {
			path = "file://"+localPath;
			root = VFS.getManager().resolveFile(path);
		} catch (FileSystemException e) {
			e.printStackTrace();
		}
	}

	public String getPath() {
		return path;
	}

	public void addIndexer(IndexHandler handler) {
		indexers.add(handler);
	}
	
	@SallyService(channel="/configure")
	public void getConfigUrl(String op, SallyActionAcceptor acceptor, SallyContext context) {
		acceptor.acceptResult(new ConfigMeta("pm", "http://localhost:8080/projectmanager", "Configure current project"));
	}
	
	@SallyService(channel="/project")
	public void getProjectRoot(String op, SallyActionAcceptor acceptor, SallyContext context) {
		if (op.equals("get")) {
			acceptor.acceptResult(this);
		}
	}
	
	@SallyService(channel="/project/setPath")
	public void setProjectRoot(String newPath, SallyActionAcceptor acceptor, SallyContext context) {
		path = newPath;
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

	
	@SallyService(channel="/project/getFile")
	public void getProjectFile(String fileURI, SallyActionAcceptor acceptor, SallyContext context) {
		if (fileURI.startsWith(path)) {
			try {
				FileObject resolvedFile = root.resolveFile(fileURI);
				if (resolvedFile != null) {
					acceptor.acceptResult(getContent(resolvedFile.getContent().getInputStream()));
				}
			} catch (FileSystemException e) {
				e.printStackTrace();
			}
		}
	}
	

}
