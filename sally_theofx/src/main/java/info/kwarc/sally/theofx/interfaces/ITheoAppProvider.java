package info.kwarc.sally.theofx.interfaces;

import info.kwarc.sally.theofx.TheoApp;
import javafx.scene.web.WebEngine;

public interface ITheoAppProvider {
	TheoApp create(Long processInstanceID, WebEngine contentEngine);
}
