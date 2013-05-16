package info.kwarc.sally.projects;
import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyService;

import org.apache.commons.vfs2.FileObject;
import org.apache.commons.vfs2.FileSystemException;
import org.apache.commons.vfs2.VFS;



public class ProjectService {

	FileObject root;
	
	public ProjectService(String localPath) {
		try {
			root = VFS.getManager().resolveFile("file://"+localPath);
		} catch (FileSystemException e) {
			e.printStackTrace();
		}
	}

	@SallyService(channel="/project")
	public void getProjectRoot(String op, SallyActionAcceptor acceptor, SallyContext context) {
		if (op.equals("get")) {
			acceptor.acceptResult(root);
		}
	}

}
