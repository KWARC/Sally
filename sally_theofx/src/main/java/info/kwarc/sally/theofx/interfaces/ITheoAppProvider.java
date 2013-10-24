package info.kwarc.sally.theofx.interfaces;

import javafx.scene.web.WebEngine;
import info.kwarc.sally.theofx.TheoApp;

public interface ITheoAppProvider {
	TheoApp create(Long processInstanceID, WebEngine contentEngine);
}
