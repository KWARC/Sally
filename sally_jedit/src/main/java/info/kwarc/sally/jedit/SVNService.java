package info.kwarc.sally.jedit;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyService;

import java.io.File;
import java.util.HashMap;

import org.tmatesoft.svn.core.SVNException;
import org.tmatesoft.svn.core.wc.SVNClientManager;
import org.tmatesoft.svn.core.wc.SVNInfo;
import org.tmatesoft.svn.core.wc.SVNRevision;

import sally.FileRef;

public class SVNService {
	HashMap<String, String> local2svn;

	public SVNService() {
		local2svn = new HashMap<String, String>();
	}

	@SallyService(channel="get/versions")
	public void SVNFileTranslator(FileRef f, SallyActionAcceptor acceptor, SallyContext context) {
		if (local2svn.containsKey(f.getResourceURI())) {
			String URL = local2svn.get(f.getResourceURI());
			if (URL.length() == 0) // was tried before and failed
				return;
			acceptor.acceptResult(FileRef.newBuilder().setMime(f.getMime())
													  .setResourceURI(local2svn.get(f.getResourceURI())).build());
			return;
		}
		try {
			SVNInfo info = 
					SVNClientManager.newInstance().
					getWCClient().doInfo(new File("/home/costea/repos/sissi/winograd"), SVNRevision.HEAD);
			local2svn.put(f.getResourceURI(), info.getURL().toDecodedString());
		} catch (SVNException e) {
			local2svn.put(f.getResourceURI(), "");
		}
		
	}
}
