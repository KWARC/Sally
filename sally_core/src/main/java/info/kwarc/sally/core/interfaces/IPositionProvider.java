package info.kwarc.sally.core.interfaces;

import info.kwarc.sally.core.comm.Coordinates;

public interface IPositionProvider {
	Coordinates getRecommendedPosition();
	void setRecommendedCoordinates(Coordinates pos);
}
