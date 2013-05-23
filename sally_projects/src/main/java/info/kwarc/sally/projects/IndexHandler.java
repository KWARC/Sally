package info.kwarc.sally.projects;

import javax.tools.FileObject;

public interface IndexHandler {
	void restart(FileObject root);
	void getLog();
	void destroy();
}
