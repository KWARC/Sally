package info.kwarc.sally.projects;

import info.kwarc.sally.core.net.INetworkSender;
import sally.ProjectModel;


public interface ProjectFactory {
	public ProjectModule create(String filePath, ProjectModel data, INetworkSender networkSender);
}
