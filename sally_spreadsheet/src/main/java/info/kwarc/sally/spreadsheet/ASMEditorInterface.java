package info.kwarc.sally.spreadsheet;

import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyContextManager;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.networking.cometd.CometD;
import info.kwarc.sally.networking.cometd.TemplateRequest;
import info.kwarc.sally.planetary.ListOntologyConcepts;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import javax.ws.rs.FormParam;
import javax.ws.rs.GET;
import javax.ws.rs.POST;
import javax.ws.rs.Path;
import javax.ws.rs.QueryParam;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.Cookie;
import sally.RangeSelection;
import sally.TheoChangeWindow;
import freemarker.template.TemplateException;

@Path("/asmeditor")
public class ASMEditorInterface {

	String name;
	String ontology;
	Logger log;

	public ASMEditorInterface() {
		log = LoggerFactory.getLogger(ASMEditorInterface.class);
	}

	@GET
	public String generateUI(@QueryParam("s") String token) throws IOException, TemplateException {
		SallyContext context = SallyContextManager.getInstance().getContext(token);
		if (context == null) {
			return "invalid session";
		}

		RangeSelection cellPosition = context.getContextVar("ASMCellRange", RangeSelection.class);
		if (cellPosition == null) {
			return "session did not provide a valid cell range";
		}

		ASMEditorInterface formData = context.getContextVar("ASMFormData", ASMEditorInterface.class);
		if (formData == null) {
			formData = this;
			context.setContextVar("ASMFormData", formData);
		}
		SallyInteraction interaction = CometD.getInteraction();

		Map<String, String> templateData = new HashMap<String, String>();
		templateData.put("Sheet", cellPosition.getSheet());
		templateData.put("StartRow", Integer.toString(cellPosition.getStartRow()));
		templateData.put("StartCol", Integer.toString(cellPosition.getStartCol()));
		templateData.put("EndRow", Integer.toString(cellPosition.getEndRow()));
		templateData.put("EndCol", Integer.toString(cellPosition.getEndCol()));
		templateData.put("token", token);

		return interaction.getOneInteraction("/template", new TemplateRequest("asmeditor/asmeditor.ftl", templateData), String.class);
	}

	@POST
	public String respond(@FormParam("s") String token, @FormParam("action") String action, @FormParam("name") String name, @FormParam("ontology") String ontology){
		SallyContext context = SallyContextManager.getInstance().getContext(token);
		if (context == null) {
			return "invalid session";
		}

		SallyInteraction interaction = context.getCurrentInteraction();

		this.name = name;
		this.ontology = ontology;

		if (action.equals("Browse")) {
			log.debug("About to execute browse");
			String url = interaction.getOneInteraction(new ListOntologyConcepts(), String.class);
			log.debug("URL "+url);
			if (url == null)
				return null;
			TheoChangeWindow.Builder op = TheoChangeWindow.newBuilder().setUrl(url);

			Cookie cookie = context.getContextVar("Cookie", Cookie.class);
			if (cookie != null)
				op.setCookie(cookie);

			Integer wndID = context.getContextVar("ACMEditorWindowID", Integer.class);
			if (wndID != null)
				op.setWindowid(wndID);

			interaction.getOneInteraction(op.build(), Boolean.class);

		}

		return "ok";
	}
}
