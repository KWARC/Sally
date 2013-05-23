package info.kwarc.sally.networking.cometd;

import info.kwarc.sally.core.SallyInteraction;

import java.util.HashMap;
import java.util.List;

import javax.ws.rs.GET;
import javax.ws.rs.Path;

@Path("configure")
public class SallyConfigure {

	@GET
	public String generateConfig() {
		SallyInteraction interaction = CometD.getInteraction();
		List<ConfigMeta> configurations = interaction.getPossibleInteractions("/configure", "get", ConfigMeta.class);
		HashMap<String, Object> templateMap = new HashMap<String, Object>();
		templateMap.put("configs", configurations);
		return interaction.getOneInteraction("/template/generate", new TemplateRequest("/config/config.tpl", templateMap), String.class);
	}
}
