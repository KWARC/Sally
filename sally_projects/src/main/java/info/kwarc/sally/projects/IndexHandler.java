package info.kwarc.sally.projects;

import org.apache.commons.vfs2.FileObject;


public interface IndexHandler {
	void restart(FileObject root);
	void getLog();
	void destroy();
}
