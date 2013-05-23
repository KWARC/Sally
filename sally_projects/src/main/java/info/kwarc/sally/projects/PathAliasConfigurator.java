package info.kwarc.sally.projects;

import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.networking.cometd.CometD;
import info.kwarc.sally.networking.cometd.TemplateRequest;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import javax.ws.rs.FormParam;
import javax.ws.rs.GET;
import javax.ws.rs.POST;
import javax.ws.rs.Path;

@Path("aliasmanager")
public class PathAliasConfigurator {
	
	@GET
	public String generatePage() {
		SallyInteraction interaction = CometD.getInteraction();
		List<String> aliases = interaction.getPossibleInteractions("/alias/list", "get", String.class);
		HashMap<String, Object> templateData = new HashMap<String, Object>();
		templateData.put("aliases", aliases);
		templateData.put("msg", interaction.getContext().getContextVar("msg"));
		interaction.getContext().setContextVar("msg", null);
		return interaction.getOneInteraction("/template/generate", new TemplateRequest("projects/aliasmanager.tpl", templateData), String.class);
	}
	
	@POST
	public String saveSettings(@FormParam(value="keys[]") List<String> keys, @FormParam(value = "values[]") List<String> values) {
		SallyInteraction interaction = CometD.getInteraction();
		List<String> newList = new ArrayList<String>();
		if (keys.size() != values.size()) {
			return "Invalid query";
		}
		for (int i=0; i<keys.size(); ++i) {
			String key = keys.get(i).trim();
			String value = values.get(i).trim();
			if (key.length() == 0 || value.length() == 0)
				continue;
			newList.add(key+"@"+value);
		}
		interaction.getOneInteraction("/alias/set", newList, Boolean.class);
		return generatePage();
	}
}
