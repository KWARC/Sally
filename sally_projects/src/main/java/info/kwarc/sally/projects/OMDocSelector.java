package info.kwarc.sally.projects;
import org.apache.commons.vfs2.FileSelectInfo;
import org.apache.commons.vfs2.FileSelector;
import org.apache.commons.vfs2.FileType;


public class OMDocSelector implements FileSelector {

	public boolean includeFile(FileSelectInfo fileInfo) throws Exception {
		return fileInfo.getFile().getName().getExtension().equals("omdoc");
	}

	public boolean traverseDescendents(FileSelectInfo fileInfo) throws Exception {
		if (fileInfo.getFile().getType() == FileType.FOLDER && fileInfo.getFile().getName().equals(".svn"))
			return false;
		else
			return true;
	}
	
}
