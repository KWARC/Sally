package info.kwarc.sally.service.def_lookup;

import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.planetary.Planetary;

import java.util.HashMap;

import sally.MMTUri;

import com.google.inject.Inject;

public class DefinitionLookupService {
	Planetary planetary;
	ISallyWorkflowManager kb;

	@Inject
	public DefinitionLookupService(Planetary planetary, ISallyWorkflowManager kb) {
		this.kb = kb;
		this.planetary = planetary;
	}

	public String getDefinitionLookupURL(String uri) {
		if (uri.contains("?")) {
			uri = uri.substring(0, uri.indexOf('?'));
		}

		return planetary.getPlanetaryRoot()+"/mmt/archives?q="+uri;
	}

	@SallyService
	public void planetaryServices(final MMTUri mmtURI, SallyInteractionResultAcceptor acceptor, final SallyContext context) {
		acceptor.acceptResult(new SallyMenuItem("Knowledge Base", "Definition Lookup", "Look up definition associated to the selected object") {
			public void run() {
				Long parentProcessInstanceID = context.getContextVar("processInstanceId", Long.class);

				HashMap<String, Object>  input = new  HashMap<String, Object>();
				input.put("wndURLInput", getDefinitionLookupURL(mmtURI.getUri()));
				kb.startProcess(parentProcessInstanceID, "Sally.deflookup", input);
			}
		});
	}


}
