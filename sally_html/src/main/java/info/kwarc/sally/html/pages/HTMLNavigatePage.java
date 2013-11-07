package info.kwarc.sally.html.pages;

import info.kwarc.sally.core.DocumentManager;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.networking.TemplateEngine;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import java.util.HashMap;
import java.util.Map;

import javax.ws.rs.GET;
import javax.ws.rs.Path;
import javax.ws.rs.QueryParam;

import org.drools.runtime.process.ProcessInstance;
import org.slf4j.Logger;

import com.google.inject.Inject;

@Path("sally/html/navigate")
public class HTMLNavigatePage {

	Logger log;
	TemplateEngine te;
	ISallyWorkflowManager kb;
	DocumentManager docMan;
	
	@Inject
	public HTMLNavigatePage(TemplateEngine te, ISallyWorkflowManager kb, DocumentManager docMan) {
		this.te = te;
		log = org.slf4j.LoggerFactory.getLogger(getClass());
		this.kb = kb;
		this.docMan = docMan;
	}

	@GET
	public String get(@QueryParam("id") String _pid){
		Long pid = Long.parseLong(_pid);
		ProcessInstance pi = kb.getProcessInstance(pid);
		Map<String, Object> vars = HandlerUtils.getProcessVariables(pi);
		HashMap<String, Object> input = new HashMap<String, Object>();
		input.putAll(vars);;
		input.put("pid", pid);
		return te.generateTemplate("instances/instances.ftl", input);
	}
}
