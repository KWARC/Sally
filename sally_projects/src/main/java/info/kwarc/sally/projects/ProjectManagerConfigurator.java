package info.kwarc.sally.projects;

import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.networking.cometd.CometD;
import info.kwarc.sally.networking.cometd.TemplateRequest;

import java.util.HashMap;
import java.util.List;

import javax.ws.rs.FormParam;
import javax.ws.rs.GET;
import javax.ws.rs.POST;
import javax.ws.rs.Path;

@Path("projectmanager")
public class ProjectManagerConfigurator {
	@GET
	public String generatePage() {
		SallyInteraction interaction = CometD.getInteraction();
		Project project = interaction.getOneInteraction("/project", "get", Project.class);
		
		List<String> indexes = interaction.getPossibleInteractions("/indexes", "get", String.class);
		if (project == null) {
			project = new Project("");
			interaction.registerServices(project);
		}
		HashMap<String, Object> templateData = new HashMap<String, Object>();
		templateData.put("root", project.getPath());
		templateData.put("indexes", indexes);
		return interaction.getOneInteraction("/template/generate", new TemplateRequest("projects/projectmanager.tpl", templateData), String.class);
	}
	
	@POST
	public String doUpdate(@FormParam(value="root") String root) {
		SallyInteraction interaction = CometD.getInteraction();
		interaction.getOneInteraction("/project/setPath", root, String.class);
		
		return generatePage();
	}
}
