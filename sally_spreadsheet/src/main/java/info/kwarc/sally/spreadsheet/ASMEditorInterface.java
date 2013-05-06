package info.kwarc.sally.spreadsheet;

import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyContextManager;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.networking.cometd.CometD;
import info.kwarc.sally.planetary.ListOntologyConcepts;

import java.io.IOException;
import java.io.StringWriter;
import java.net.URI;
import java.util.HashMap;
import java.util.Map;

import javax.ws.rs.FormParam;
import javax.ws.rs.GET;
import javax.ws.rs.POST;
import javax.ws.rs.Path;
import javax.ws.rs.QueryParam;
import javax.ws.rs.core.Response;

import sally.RangeSelection;
import freemarker.template.Template;
import freemarker.template.TemplateException;

@Path("/asmeditor")
public class ASMEditorInterface {

	String name;
	String ontology;
	
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
		
		Template t = CometD.getTemplatingEngine().getTemplate("asmeditor/asmeditor.ftl");
		StringWriter w = new StringWriter();

		Map<String, String> templateData = new HashMap<String, String>();
		templateData.put("Sheet", cellPosition.getSheet());
		templateData.put("StartRow", Integer.toString(cellPosition.getStartRow()));
		templateData.put("StartCol", Integer.toString(cellPosition.getStartCol()));
		templateData.put("EndRow", Integer.toString(cellPosition.getEndRow()));
		templateData.put("EndCol", Integer.toString(cellPosition.getEndCol()));
		templateData.put("token", token);
		
		t.process(templateData, w);
		return w.toString();
	}
	
	@POST
	public Response respond(@FormParam("s") String token, @FormParam("action") String action, @FormParam("name") String name, @FormParam("ontology") String ontology){
		SallyContext context = SallyContextManager.getInstance().getContext(token);
		if (context == null) {
			return Response.ok("invalid session").build();
		}
		
		SallyInteraction interaction = context.getCurrentInteraction();
		
		this.name = name;
		this.ontology = ontology;
		
		if (action.equals("Browse")) {
			String url = interaction.getOneInteraction(new ListOntologyConcepts(), String.class);
			return Response.temporaryRedirect(URI.create(url)).build();
		}
		
		return Response.ok("ok").build();
	}
}
