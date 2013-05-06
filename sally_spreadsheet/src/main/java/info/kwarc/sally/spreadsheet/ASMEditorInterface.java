package info.kwarc.sally.spreadsheet;

import freemarker.template.Template;
import freemarker.template.TemplateException;
import info.kwarc.sally.networking.cometd.CometD;

import java.io.IOException;
import java.io.StringWriter;

import javax.ws.rs.GET;
import javax.ws.rs.Path;

@Path("/asmeditor")
public class ASMEditorInterface {

	@GET
	public String generateUI() throws IOException, TemplateException {
		Template t = CometD.getTemplatingEngine().getTemplate("asmeditor.ftm");
		StringWriter w = new StringWriter();
		t.process(null, w);
		return w.toString();
	}
	
}
